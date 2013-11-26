/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_context.h

Abstract:

    SPACER for datalog

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-20.

Revision History:

--*/

#ifndef _SPACER_CONTEXT_H_
#define _SPACER_CONTEXT_H_

#ifdef _CYGWIN
#undef min
#undef max
#endif
#include <queue>
#include "spacer_manager.h"
#include "spacer_prop_solver.h"
#include "spacer_reachable_cache.h"
#include "fixedpoint_params.hpp"


namespace datalog {
    class rule_set;
    class context;
};

namespace spacer {

    class pred_transformer;
    class model_node;
    class derivation;
    class model_search;
    class context;

    typedef obj_map<datalog::rule const, app_ref_vector*> rule2inst;
    typedef obj_map<func_decl, pred_transformer*> decl2rel;

    enum LOCAL_REACH_RESULT {
        REACH,
        UNREACH,
        ABS_REACH,
        UNKN
    };

    // 
    // Predicate transformer state.
    // A predicate transformer corresponds to the 
    // set of rules that have the same head predicates.
    // 
    
    class pred_transformer {

        struct stats {
            unsigned m_num_propagations;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        typedef obj_map<datalog::rule const, expr*> rule2expr;
        typedef obj_map<datalog::rule const, ptr_vector<app> > rule2apps;

        manager&                     pm;        // spacer-manager
        ast_manager&                 m;         // manager
        context&                     ctx;
        
        func_decl_ref                m_head;    // predicate 
        func_decl_ref_vector         m_sig;     // signature
        ptr_vector<pred_transformer> m_use;     // places where 'this' is referenced.
        ptr_vector<datalog::rule>    m_rules;   // rules used to derive transformer
        prop_solver                  m_solver;  // solver context
        scoped_ptr<smt_context>      m_reach_ctx; // context for reachability facts
        vector<expr_ref_vector>      m_levels;  // level formulas
        expr_ref_vector              m_reach_facts; // reach facts
        expr_ref_vector              m_invariants;      // properties that are invariant.
        obj_map<expr, unsigned>      m_prop2level;      // map property to level where it occurs.
        obj_map<expr, datalog::rule const*> m_tag2rule; // map tag predicate to rule. 
        rule2expr                    m_rule2tag;        // map rule to predicate tag.
        rule2inst                    m_rule2inst;       // map rules to instantiations of indices
        rule2expr                    m_rule2transition; // map rules to transition 
        rule2apps                    m_rule2vars;       // map rule to auxiliary variables
        expr_ref                     m_transition;      // transition relation.
        expr_ref                     m_initial_state;   // initial state.
        bool                         m_all_init;        // true if the pt has no uninterpreted body in any rule
        //reachable_cache              m_reachable; 
        ptr_vector<func_decl>        m_predicates;
        stats                        m_stats;
        expr_ref_vector              m_reach_case_assumps; // aux vars for asserting reach facts in m_reach_ctx and children's m_solver's incrementally
        vector<u_map<expr*> >        m_o_reach_case_maps;
                                        // maps from o-idx to o-versions of the assumptions;
                                        // #o-indices = max number of times this
                                        // predicate appears as a body predicate
                                        // in any rule
        expr_ref_vector              _o_reach_case_assumps; // dummy to have references to the o-versions

        void init_sig();
        void ensure_level(unsigned level);
        bool add_property1(expr * lemma, unsigned lvl);  // add property 'p' to state at level lvl.
        void add_child_property(pred_transformer& child, expr* lemma, unsigned lvl, bool is_reach_fact = false); 
        void mk_assumptions(func_decl* head, expr* fml, expr_ref_vector& result, bool is_reach_fact = false);

        // Initialization
        void init_rules(decl2rel const& pts, expr_ref& init, expr_ref& transition);
        void init_rule(decl2rel const& pts, datalog::rule const& rule, vector<bool>& is_init,                                      
                       ptr_vector<datalog::rule const>& rules, expr_ref_vector& transition);
        void init_atom(decl2rel const& pts, app * atom, app_ref_vector& var_reprs, expr_ref_vector& conj, unsigned tail_idx);

        void simplify_formulas(tactic& tac, expr_ref_vector& fmls);

        // Debugging
        bool check_filled(app_ref_vector const& v) const;
        
        void add_premises(decl2rel const& pts, unsigned lvl, datalog::rule& rule, expr_ref_vector& r);

        expr* mk_fresh_reach_case_assump () const;

    public:
        pred_transformer(context& ctx, manager& pm, func_decl* head);
        ~pred_transformer();

        void add_rule(datalog::rule* r) { m_rules.push_back(r); }
        void add_use(pred_transformer* pt) { if (!m_use.contains(pt)) m_use.insert(pt); }
        void initialize(decl2rel const& pts);

        func_decl* head() const { return m_head; }
        ptr_vector<datalog::rule> const& rules() const { return m_rules; }
        func_decl* sig(unsigned i) const { return m_sig[i]; } // signature 
        func_decl* const* sig() { return m_sig.c_ptr(); }
        unsigned  sig_size() const { return m_sig.size(); }
        expr*  transition() const { return m_transition; }
        expr*  initial_state() const { return m_initial_state; }
        expr*  rule2tag(datalog::rule const* r) { return m_rule2tag.find(r); }
        unsigned get_num_levels() { return m_levels.size(); }
        expr_ref get_cover_delta(func_decl* p_orig, int level);
        void     add_cover(unsigned level, expr* property);
        expr* get_reach ();

        // add all lemmas from level up to infty to forms;
        // use the o-index idx while adding
        void add_lemmas (int level, int idx, expr_ref_vector& forms) const;

        std::ostream& display(std::ostream& strm) const;

        void collect_statistics(statistics& st) const;
        void reset_statistics();

        bool is_reachable_known (expr* state);
        bool is_reachable_with_reach_facts (model_node& n, datalog::rule const& r);
        void get_reach_explanation (model_ref& M, expr_ref& reach_fact);
        expr* get_used_reach_facts (model_ref const& M, unsigned oidx) const;
        void remove_predecessors(expr_ref_vector& literals);
        void find_predecessors(datalog::rule const& r, ptr_vector<func_decl>& predicates) const;
        void find_predecessors(vector<std::pair<func_decl*, unsigned> >& predicates) const;
        datalog::rule const& find_rule(model_core const& model) const;
        void find_rules (model_core const& model, svector<datalog::rule const*>& rules) const;
        expr* get_transition(datalog::rule const& r) { return m_rule2transition.find(&r); }
        ptr_vector<app>& get_aux_vars(datalog::rule const& r) { return m_rule2vars.find(&r); }

        bool propagate_to_next_level(unsigned level);
        void propagate_to_infinity(unsigned level);
        void add_property(expr * lemma, unsigned lvl);  // add property 'p' to state at level.
        expr* mk_o_reach_case_assump (unsigned idx, unsigned oidx);
        expr* get_reach_case_assump (unsigned idx) const;
        unsigned get_num_reach_cases () const;

        void add_reach_fact (expr* fact);  // add reachability fact
        bool assert_reach_facts (expr_ref_vector& assumps) const;
        bool assert_o_reach_facts (expr_ref_vector& assumps, unsigned oidx) const;

        LOCAL_REACH_RESULT is_reachable(model_node& n, expr_ref_vector* core, bool& uses_level);
        bool is_invariant(unsigned level, expr* co_state, bool inductive, bool& assumes_level, expr_ref_vector* core = 0);
        bool check_inductive(unsigned level, expr_ref_vector& state, bool& assumes_level);

        expr_ref get_formulas(unsigned level, bool add_axioms);

        void simplify_formulas();

        expr_ref get_propagation_formula(decl2rel const& pts, unsigned level);

        manager& get_spacer_manager() const { return pm; }
        ast_manager& get_manager() const { return m; }

        void add_premises(decl2rel const& pts, unsigned lvl, expr_ref_vector& r);

        void close(expr* e);

        app_ref_vector& get_inst(datalog::rule const* r) { return *m_rule2inst.find(r);}

        void inherit_properties(pred_transformer& other);

        void ground_free_vars(expr* e, app_ref_vector& vars, ptr_vector<app>& aux_vars);

        prop_solver& get_solver() { return m_solver; }

    };


    /**
     * type of derivation for a model node
     */
    /*enum MODEL_NODE_TYPE {
        UNDER,  // use an under-approximating summary
        OVER,   // use an over-approximating summary
        EXPAND  // expand the search tree
    };*/


    /**
     * goal node (perhaps, rename to goal_node?)
     *      find a pre(image), given a post and a post_ctx;
     *      this is done by means of a derivation to <post,post_ctx>
     */
    class model_node {
        model_node*             m_parent;
        pred_transformer&       m_pt;
        ast_manager&            m;
        expr_ref                m_post;
        //expr_ref                m_pre;
        unsigned                m_level;       
        bool                    m_open;     // whether a concrete answer to the goal is found
        ptr_vector<derivation>  m_derivs;   // all derivations being tried out
        derivation*             m_my_deriv; // the derivation which contains me as a premise
        //derivation const*       m_closing_deriv; // the derivation which closes the node
        //MODEL_NODE_TYPE         m_type;     // type of derivation
        bool                    m_in_q;     // iff this node is currently in the search queue
        model_search&           m_search;
        bool                    m_reachable;

        // unique id of this node and a global count of all goal nodes;
        // count is expected to be reset at every level of query
        //unsigned                m_id;
        //static unsigned         m_count;

    public:
        model_node (model_node* parent, pred_transformer& pt, unsigned level, derivation* deriv, model_search& search):
            m_parent (parent), m_pt (pt), m (m_pt.get_manager ()),
            m_post (m),
            //m_post_ctx (m), m_pre (m),
            m_level (level), m_open (true),
            m_my_deriv (deriv),
            //m_closing_deriv (0),
            //m_type (EXPAND),
            m_in_q (false),
            m_search (search),
            m_reachable (false)
            //m_id (m_count+1)
        { //m_count++;
        }

        ~model_node ();

        bool operator> (model_node const& x) const { return level () > x.level (); }

        //static void reset_count () { m_count = 0; }
        /*static bool is_ghost (func_decl const* d)
            { return d && d->get_name ().str ().compare (0, 6, "ghost_") == 0; }*/

        model_node* parent () const { return m_parent; }
        pred_transformer& pt () const { return m_pt; }
        ast_manager& get_manager () const { return m; }
        manager& get_spacer_manager () const { return m_pt.get_spacer_manager (); }
        expr_ref const& post () const { return m_post; }
        //expr_ref const& pre () const { return m_pre; }
        //bool has_pre () const { return m_pre; }
        derivation* my_deriv () const { return m_my_deriv; }
        //derivation const* closing_deriv () const { return m_closing_deriv; }
        bool is_open () const { return m_open; }
        bool is_closed () const { return !m_open; }
        unsigned level () const { return m_level; }

        void incr_level () { m_level++;}

        void add_deriv (derivation* deriv) { m_derivs.push_back (deriv); }
        void updt_parent (model_node* parent) { m_parent = parent; }
        void updt_post (expr_ref const& post) { m_post = post; }
        //void updt_type (MODEL_NODE_TYPE t) { m_type = t; }
        //void updt_pre (expr_ref const& pre) { m_pre = pre; }

        void reset () {
            //m_pre.reset ();
            del_derivs ();
            open ();
        }

        void close ();
        void open () { m_open = true; }

        void inq () { m_in_q = true; }
        void outq () { m_in_q = false; }
        bool is_inq () const { return m_in_q; }

        void del_derivs ();
        // delete only those derivations containing pt at level
        void del_derivs (pred_transformer const& pt, unsigned level);
        // delete just the given derivation
        void del_derivs (derivation* d);
        // delete all derivations except the given one
        void del_derivs_except (derivation* d);

        bool has_derivs () const { return !m_derivs.empty (); }
        // has any derivation with curr premise at level
        bool has_derivs (unsigned level) const;

        unsigned num_derivs () const { return m_derivs.size (); }

        bool is_reachable () const { return is_closed () && m_reachable; }
        bool is_unreachable () const { return is_closed () && !m_reachable; }
        void set_reachable () { m_reachable = true; }
        void set_unreachable () { m_reachable = false; }

        // util

        // one could have used the memory address of the object instead of a
        // separate counter, but it might pose problems when an object is
        // deleted and another one constructed at the same address, as the ids
        // may persist beyond the lifetime of the object
        //unsigned id () const { return m_id; }

        // return a constant with name 'ghost_<n>_<str>' where n is a unique id
        // for (this) and str is the name of the given app
        /*app* mk_ghost (app* a) const {
            SASSERT (a->get_num_args () == 0); // it's a constant
            func_decl* fd = a->get_decl ();
            sort* s = fd->get_range ();
            symbol const& old_sym = fd->get_name ();
            std::stringstream new_name;
            new_name << "ghost_" << id () << "_" << old_sym.str ();
            return m.mk_const (symbol (new_name.str ().c_str ()), s);
        }*/
    };


    /**
     * a derivation class for <m_concl.post, m_concl.post_ctx>
     * prems are the premises needed to be derived (corresponding to a horn
     * clause for m_concl.pt()) in order to reach concl.post
     */
    class derivation {
        typedef std::pair<app_ref*, app_ref*> app_ref_ptr_pair;

        model_node*                         m_concl;// conclusion
        ptr_vector<model_node>              m_prems;// all premises which need to be derived
        vector<unsigned>                    m_o_idx;// order of o-index's to be processed
        datalog::rule const&                m_rule; // the rule from m_prems to m_concl
        ptr_vector<model_node>::iterator    m_curr_it; // the premise currently being processed
        ast_manager&                        m;
        manager&                            m_sm;
        //vector<vector<app_ref_vector> >     m_ghosts;
                        // for each o_index, vector of (o_const, ghost) pairs
        expr_ref                            m_post; // combined goal for m_prems
        vector<app_ref_vector>              m_ovars;
        vector<app_ref_vector>              m_nvars;
        model_ref                           M;

        // substitute o-consts in phi by ghosts;
        // resets m_ghosts and updates it for phi
        //void ghostify (expr_ref& phi);

        // populate m_ghosts for phi
        //void mk_ghosts (expr_ref const& phi);
        // utility method
        //void mk_ghosts (ast_mark& mark, ptr_vector<expr>& todo, expr* e);

        // mk substitution based on m_ghosts
        //void mk_ghost_sub (expr_substitution& sub) const;
        // mk substitution to replace ghosts by n-versions of o-consts for the pt at curr_o_idx ()
        //void mk_unghost_sub (expr_substitution& sub) const;

        model_node& next () {
            if (is_last ()) throw default_exception ("No next premise");
            if (m_curr_it == m_prems.end ()) m_curr_it = m_prems.begin ();
            else m_curr_it++;
            return **m_curr_it;
        }

        model_node& prev () {
            if (is_first ()) throw default_exception ("No prev premise");
            m_curr_it--;
            return **m_curr_it;
        }

    public:
        derivation (model_node* concl,
                    ptr_vector<pred_transformer>& pred_pts,
                    vector<unsigned> pred_o_idx,
                    datalog::rule const& rule,
                    model_search& search);

        ~derivation ();

        bool has_next () const { return (m_prems.size () > 0 && m_curr_it+1 != m_prems.end ()); }
        bool has_prev () const { return m_curr_it != m_prems.begin (); }
        bool is_first () const { return !has_prev (); }
        bool is_last () const { return !has_next (); }

        // o_idx of the pt at m_curr_it
        unsigned curr_o_idx () const {
            return m_o_idx [m_curr_it-m_prems.begin ()];
        }

        unsigned num_prems () const { return m_prems.size (); }

        model_node& curr () const { return **m_curr_it; }

        ptr_vector<model_node> const& prems () const { return m_prems; }

        // iff every premise (up to and including m_curr_it) is closed
        bool is_closed () const {
            for (ptr_vector<model_node>::const_iterator it = m_prems.begin ();
                    it <= m_curr_it; it++) {
                if ((*it)->is_open ()) return false;
            }
            return true;
        }

        // has a premise with given pt and level
        bool has_prem (pred_transformer const& pt, unsigned level) const {
            for (ptr_vector<model_node>::const_iterator it = m_prems.begin ();
                    it != m_prems.end (); it++) {
                if ((*it)->level () == level &&
                        (*it)->pt ().head () == pt.head ())
                    return true;
            }
            return false;
        }

        // we need to check if phi is reachable by m_prems;
        //   we already know that phi can reach m_concl.post
        void setup (expr_ref& phi, model_ref& M);

        //expr_ref const& post () const { return m_post; }

        // make post (phi) and post_ctx (ctx) for the next premise
        //void mk_prem_post (expr_ref& phi, expr_ref& ctx) const;
        model_node& mk_next (expr_ref& post);

        datalog::rule const& get_rule () const { return m_rule; }

        // get symbolic cex for the derivation to m_concl.post
        //void get_trace (expr_ref_vector& trace_conjs) const;
    };


    class model_node_comparison {
    public:
        model_node_comparison () {}

        // TODO: for nodes at the same level, consider shortest path distance of
        // m_pt from a pt with init rule
        bool operator () (model_node const* n1, model_node const* n2) const {
            return (*n1) > (*n2);
        }
    };

    /**
     * priority queue is a max-heap; so, use > relation to order nodes
     *
     * we need an erase method to remove arbitrary nodes from the queue
     */
    class model_node_ptr_queue :
        public std::priority_queue <model_node*,
                                    std::vector<model_node*>,
                                    model_node_comparison> {
        public:
            void erase (model_node* n) {
                for (std::vector<model_node*>::iterator it = c.begin (); it != c.end (); it++) {
                    if (*it == n) {
                        c.erase (it);
                        TRACE ("spacer", tout << "Erasing node from queue\n";);
                        break;
                    }
                }
            }
    };


    // TODO: this is just a wrapper around model_node_ptr_queue -- get rid off it?
    class model_search {
        model_node*             m_root;
        model_node_ptr_queue    m_leaves;
        //vector<obj_map<expr, unsigned> > m_cache;

        //obj_map<expr, unsigned>& cache(model_node const& n);
        void enqueue_leaf(model_node& n); // add leaf to priority queue.
        //void update_models();
    public:
        model_search(): m_root(0) {}
        ~model_search();

        void reset();
        model_node* next();
        //bool is_repeated(model_node& n) const;
        void add_leaf(model_node& n); // add fresh node.
        // do we really need set_leaf?
        void set_leaf(model_node& n); // Set node as leaf, remove children.
        void erase_leaf(model_node& n);

        void set_root(model_node* n);
        model_node& get_root() const { return *m_root; }
        //std::ostream& display(std::ostream& out) const; 
        expr_ref get_trace(context const& ctx);
        //proof_ref get_proof_trace(context const& ctx);
        //void backtrack_level(bool uses_level, model_node& n);
    };


    struct model_exception { };
    struct inductive_exception {};


    // 'state' is unsatisfiable at 'level' with 'core'. 
    // Minimize or weaken core.
    class core_generalizer {
    protected:
        context& m_ctx;
    public:
        typedef vector<std::pair<expr_ref_vector,bool> > cores;
        core_generalizer(context& ctx): m_ctx(ctx) {}
        virtual ~core_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level) = 0;
        virtual void operator()(model_node& n, expr_ref_vector const& core, bool uses_level, cores& new_cores) {
            new_cores.push_back(std::make_pair(core, uses_level));
            if (!core.empty()) {
                (*this)(n, new_cores.back().first, new_cores.back().second);
            }
        }
        virtual void collect_statistics(statistics& st) const {}
        virtual void reset_statistics() {}
    };


    // AK: need to clean this up!
    class context {

        struct stats {
            unsigned m_num_nodes;
            unsigned m_max_depth;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        
        smt_params&    m_fparams;
        fixedpoint_params const&    m_params;
        ast_manager&         m;
        datalog::context*    m_context;
        manager              m_pm;  
        decl2rel             m_rels;         // Map from relation predicate to fp-operator.       
        func_decl_ref        m_query_pred;
        pred_transformer*    m_query;
        mutable model_search m_search;
        lbool                m_last_result;
        unsigned             m_inductive_lvl;
        unsigned             m_expanded_lvl;
        ptr_vector<core_generalizer>  m_core_generalizers;
        stats                m_stats;
        volatile bool        m_cancel;
        model_converter_ref  m_mc;
        proof_converter_ref  m_pc;
        model_ref            m_curr_model; // sat model for the current model_node whose reachability is being checked
        
        // Functions used by search.
        void solve_impl();
        bool check_reachability(unsigned level);        
        void propagate(unsigned max_prop_lvl);
        void close_node(model_node& n);
        void check_pre_closed(model_node& n);
        void expand_node(model_node& n);
        LOCAL_REACH_RESULT expand_state(model_node& n, expr_ref_vector& cube, bool& uses_level);
        void mk_reach_fact (model_node& n, expr_ref& result);
        void create_children(model_node& n);
        expr_ref mk_sat_answer() const;
        expr_ref mk_unsat_answer() const;

        void report_unreach (model_node& ch); // ch's post is unreachable
        void report_reach (model_node& ch); // ch's post is concretely reachable
        void updt_as_reachable (model_node& n);
        bool redo_at_higher_level (model_node const& ch, derivation const* d, model_node const& par) const;
        
        // Generate inductive property
        void get_level_property(unsigned lvl, expr_ref_vector& res, vector<relation_info> & rs) const;


        // Initialization
        class classifier_proc;
        void init_core_generalizers(datalog::rule_set& rules);

        bool check_invariant(unsigned lvl);
        bool check_invariant(unsigned lvl, func_decl* fn);

        void checkpoint();

        void init_rules(datalog::rule_set& rules, decl2rel& transformers);

        void simplify_formulas();

        void reset_core_generalizers();

        void validate();

    public:       
        
        /**
           Initial values of predicates are stored in corresponding relations in dctx.
           
           We check whether there is some reachable state of the relation checked_relation.
        */
        context(
            smt_params&        fparams,
            fixedpoint_params const&  params,
            ast_manager&       m);

        ~context();
        
        smt_params&       get_fparams() const { return m_fparams; }
        fixedpoint_params const& get_params() const { return m_params; }
        ast_manager&      get_manager() const { return m; }
        manager&          get_spacer_manager() { return m_pm; }
        decl2rel const&   get_pred_transformers() const { return m_rels; }
        pred_transformer& get_pred_transformer(func_decl* p) const { return *m_rels.find(p); }
        datalog::context& get_context() const { SASSERT(m_context); return *m_context; }
        expr_ref          get_answer();

        bool              is_dl() const { return m_fparams.m_arith_mode == AS_DIFF_LOGIC; }
        bool              is_utvpi() const { return m_fparams.m_arith_mode == AS_UTVPI; }

        void collect_statistics(statistics& st) const;
        void reset_statistics();

        std::ostream& display(std::ostream& strm) const;        

        void display_certificate(std::ostream& strm) const;

        lbool solve();

        void cancel();

        void cleanup();

        void reset();

        void set_query(func_decl* q) { m_query_pred = q; }

        void set_unsat() { m_last_result = l_false; }

        void set_model_converter(model_converter_ref& mc) { m_mc = mc; }

        model_converter_ref get_model_converter() { return m_mc; }

        void set_proof_converter(proof_converter_ref& pc) { m_pc = pc; }

        void update_rules(datalog::rule_set& rules);

        void set_axioms(expr* axioms) { m_pm.set_background(axioms); }

        unsigned get_num_levels(func_decl* p);

        expr_ref get_cover_delta(int level, func_decl* p_orig, func_decl* p);

        void add_cover(int level, func_decl* pred, expr* property);

        model_ref get_model();

        proof_ref get_proof() const;

        model_node& get_root() const { return m_search.get_root(); }

        void set_curr_model (model_ref& m) { m_curr_model = m; }
        void reset_curr_model () { m_curr_model.reset (); }
        model* get_curr_model_ptr () const { return m_curr_model.get(); }
    };

};

#endif
