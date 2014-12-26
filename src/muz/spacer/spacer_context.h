/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_context.h

Abstract:

    SPACER for datalog

Author:

    Anvesh Komuravelli

Revision History:

    Based on ../pdr/pdr_context.h by
     Nikolaj Bjorner (nbjorner)

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
      
        /// Auxiliary variables to represent different disjunctive
        /// cases of must summaries. Stored over 'n' (a.k.a. new)
        /// versions of the variables
        expr_ref_vector              m_reach_case_vars; 
      
        model_evaluator              m_mev;

        // reach fact justification
        struct reach_fact_just {
            datalog::rule const& r;
            expr_ref_vector pred_reach_facts; // predecessor reach facts
            reach_fact_just (datalog::rule const& g_r, expr_ref_vector const& g_facts):
                r (g_r), pred_reach_facts (g_facts)
            {}
        };

        obj_map<expr, reach_fact_just*>     m_reach_fact_justs;

      /// evaluate v in a model
      expr_ref eval (const model_ref &model, expr * v);
      
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

        expr* mk_fresh_reach_case_var ();

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

        std::ostream& display(std::ostream& strm) const;

        void collect_statistics(statistics& st) const;
        void reset_statistics();

        bool is_reachable_known (expr* state, model_ref* model = 0);
        void get_used_reach_fact (const model_ref& M, expr_ref& reach_fact);
        void get_used_o_reach_fact (const model_ref& M, unsigned oidx, 
                                    expr_ref& o_reach_fact, expr_ref& n_reach_fact);
        datalog::rule const* get_just_rule (expr* fact);
        expr_ref_vector const* get_just_pred_facts (expr* fact);
        void remove_predecessors(expr_ref_vector& literals);
        void find_predecessors(datalog::rule const& r, ptr_vector<func_decl>& predicates) const;
        void find_predecessors(vector<std::pair<func_decl*, unsigned> >& predicates) const;
        datalog::rule const* find_rule(const model_ref &model, bool& is_concrete, 
                                       vector<bool>& reach_pred_used, 
                                       unsigned& num_reuse_reach);
        expr* get_transition(datalog::rule const& r) { return m_rule2transition.find(&r); }
        ptr_vector<app>& get_aux_vars(datalog::rule const& r) { return m_rule2vars.find(&r); }

        bool propagate_to_next_level(unsigned level);
        void propagate_to_infinity(unsigned level);
        void add_property(expr * lemma, unsigned lvl);  // add property 'p' to state at level.
        expr* get_reach_case_var (unsigned idx) const;
        unsigned get_num_reach_vars () const;

        void add_reach_fact (expr* fact, datalog::rule const& r, expr_ref_vector const& child_reach_facts);  // add reachability fact
        expr* get_last_reach_fact () const { return m_reach_facts.back (); }
        expr* get_reach_facts_assump () const;

        lbool is_reachable(model_node& n, expr_ref_vector* core, model_ref *model,
                           unsigned& uses_level, bool& is_concrete, 
                           datalog::rule const*& r, 
                           vector<bool>& reach_pred_used, 
                           unsigned& num_reuse_reach);
        bool is_invariant(unsigned level, expr* co_state, bool inductive, 
                          unsigned& solver_level, expr_ref_vector* core = 0);
        bool check_inductive(unsigned level, expr_ref_vector& state, 
                             unsigned& assumes_level);

        expr_ref get_formulas(unsigned level, bool add_axioms);

        void simplify_formulas();

        expr_ref get_propagation_formula(decl2rel const& pts, unsigned level);

        context& get_context () const {return ctx;} 
        manager& get_manager() const { return pm; }
        ast_manager& get_ast_manager() const { return m; }

        void add_premises(decl2rel const& pts, unsigned lvl, expr_ref_vector& r);

        void close(expr* e);

        app_ref_vector& get_inst(datalog::rule const* r) { return *m_rule2inst.find(r);}

        void inherit_properties(pred_transformer& other);

        void ground_free_vars(expr* e, app_ref_vector& vars, ptr_vector<app>& aux_vars);

        prop_solver& get_solver() { return m_solver; }

        expr_ref get_origin_summary (const model_ref &model, 
                                     unsigned level, unsigned oidx, bool must);
    };


  /**
   * A node in the search tree.
   */
  class model_node {
    /// parent node
    model_node*             m_parent;
    /// predicate transformer
    pred_transformer&       m_pt;
    /// post-condition decided by this node
    expr_ref                m_post;
    /// level at which to decide the post 
    unsigned                m_level;       
      
    /// whether a concrete answer to the post is found
    bool                    m_open;     
    /// when the node is closed, whether it is reachable
    bool                    m_reachable;
    
    /// optional derivation corresponding to non-linear uninterpreted
    /// part of some rule of pt
    scoped_ptr<derivation>   m_derivation;

  public:
    model_node (model_node* parent, pred_transformer& pt, unsigned level):
      m_parent (parent), m_pt (pt), 
      m_post (m_pt.get_ast_manager ()), m_level (level), 
      m_open (true), m_reachable(false) {}

    bool is_reachable () {return !m_open && m_reachable;}
    bool is_unreachable () {return !m_open && !m_reachable;}
    void set_reachable (bool v) {close (); m_reachable = v;}
    
    
    void set_derivation (derivation *d) {m_derivation = d;}
    bool has_derivation () const {return (bool)m_derivation;}
    derivation &get_derivation() const {return *m_derivation.get ();}
    void reset_derivation () {set_derivation (NULL);}
    
    model_node* parent () const { return m_parent; }
    bool is_root () const {return !(bool)m_parent;}
    
    pred_transformer& pt () const { return m_pt; }
    ast_manager& get_ast_manager () const { return m_pt.get_ast_manager (); }
    manager& get_manager () const { return m_pt.get_manager (); }
    context& get_context () const {return m_pt.get_context ();}
      
    expr* post () const { return m_post.get (); }
    unsigned level () const { return m_level; }

    void set_post (expr* post) { m_post = post; }

    void reset () 
    {
      m_derivation = NULL;
      m_open = true;
    }
    
    bool is_open () const { return m_open; }
    bool is_closed () const { return !m_open; }
    
    void close () {reset (); m_open = false;}
    void open () { reset (); }
  };


  /**
   */
  class derivation {
    /// a single premise of a derivation
    struct premise
    {
      pred_transformer &m_pt;
      /// origin order in the rule
      unsigned m_oidx;
      /// summary fact corresponding to the premise
      expr_ref m_summary;
      ///  whether this is a must or may premise
      bool m_must;
      app_ref_vector m_ovars;
      
      premise (pred_transformer &pt, unsigned oidx, expr *summary, bool must);
      premise (const premise &p);
      
      bool is_must () {return m_must;}
      expr * get_summary () {return m_summary.get ();}
      app_ref_vector &get_ovars () {return m_ovars;}
      unsigned get_oidx () {return m_oidx;}
      pred_transformer &pt () {return m_pt;} 
      
      void set_summary (expr * summary, bool must)
      {
        m_summary = summary;
        m_must = must;
      }
      
    };
    
      
    /// parent model node
    model_node&                         m_parent;
      
    ast_manager&                        m;
    manager&                            m_sm;
    const context&                      m_ctx;
    
    /// the rule corresponding to this derivation
    const datalog::rule &m_rule; 
      
    /// the premises
    vector<premise>                     m_premises;
    /// pointer to the active premise
    unsigned                            m_active;
    // transition relation over origin variables
    expr_ref                            m_trans; 

    /// -- create next child using given model as the guide
    /// -- returns NULL if there is no next child
    model_node* create_next_child (const model_ref &model);
  public:
    derivation (model_node& parent, datalog::rule const& rule, expr *trans);
    void add_premise (pred_transformer &pt, unsigned oidx, 
                      expr * summary, bool must);
    
    /// creates the first child. Must be called after all the premises
    /// are added. The model must be valid for the premises
    /// Returns NULL if no child exits
    model_node *create_first_child (const model_ref &model);
    
    /// Create the next child. Must summary of the currently active
    /// premise must be consistent with the transition relation
    model_node *create_next_child ();

    datalog::rule const& get_rule () const { return m_rule; }
    model_node& get_parent () const { return m_parent; }
  };

  class model_search {
    scoped_ptr<model_node>   m_root;
    ptr_vector<model_node> m_leaves;
      
  public:
    model_search(): m_root(NULL) {}
    ~model_search();

    void reset();
    model_node* next();
    void enqueue_leaf(model_node& n); 
    void erase_leaf(model_node& n);

    void set_root(model_node& n);
    model_node& get_root() const { return *(m_root.get ()); }
    //std::ostream& display(std::ostream& out) const; 
    expr_ref get_trace(context const& ctx);
  };


    struct model_exception { };
    struct inductive_exception {};


    // 'state' is unsatisfiable at 'level' with 'core'. 
    // Minimize or weaken core.
    class core_generalizer {
    protected:
        context& m_ctx;
    public:
        typedef vector<std::pair<expr_ref_vector,unsigned> > cores;
        core_generalizer(context& ctx): m_ctx(ctx) {}
        virtual ~core_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, unsigned& uses_level) = 0;
        virtual void operator()(model_node& n, expr_ref_vector const& core, unsigned uses_level, cores& new_cores) {
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
            unsigned m_num_queries;
            unsigned m_num_reach_queries;
            unsigned m_num_reuse_reach;
            unsigned m_max_query_lvl;
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
        model_evaluator      m_mev;
        
        // Functions used by search.
        void solve_impl();
        void solve_impl_from_lvl (unsigned from_lvl);
        bool check_reachability(unsigned level);        
        void propagate(unsigned min_prop_lvl, unsigned max_prop_lvl, 
                       unsigned full_prop_lvl);
        void expand_node(model_node& n);
        lbool expand_state(model_node& n, expr_ref_vector& core, model_ref &model, 
                           unsigned& uses_level, bool& is_concrete, 
                           datalog::rule const*& r, vector<bool>& reach_pred_used, 
                           unsigned& num_reuse_reach);
        void mk_reach_fact (model_node& n, const model_ref &model, 
                            datalog::rule const& r, expr_ref& result, 
                            expr_ref_vector& child_reach_facts);
        void create_children(model_node& n, datalog::rule const& r, const model_ref model, 
                             const vector<bool>& reach_pred_used);
        expr_ref mk_sat_answer() const;
        expr_ref mk_unsat_answer() const;

        // Generate inductive property
        void get_level_property(unsigned lvl, expr_ref_vector& res, 
                                vector<relation_info> & rs) const;


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
        ast_manager&      get_ast_manager() const { return m; }
        manager&          get_manager() { return m_pm; }
        decl2rel const&   get_pred_transformers() const { return m_rels; }
        pred_transformer& get_pred_transformer(func_decl* p) const 
        { return *m_rels.find(p); }
        datalog::context& get_datalog_context() const 
        { SASSERT(m_context); return *m_context; }
        expr_ref          get_answer();
        /**
         * get bottom-up (from query) sequence of ground predicate instances
         * (for e.g. P(0,1,0,0,3)) that together form a ground derivation to query
         */
        expr_ref          get_ground_sat_answer ();

        bool              is_dl() const { return m_fparams.m_arith_mode == AS_DIFF_LOGIC; }
        bool              is_utvpi() const { return m_fparams.m_arith_mode == AS_UTVPI; }

        void collect_statistics(statistics& st) const;
        void reset_statistics();

        std::ostream& display(std::ostream& strm) const;        

        void display_certificate(std::ostream& strm) const;

        lbool solve();

        lbool solve_from_lvl (unsigned from_lvl);

        void cancel();

        void cleanup();

        void reset();

        void set_query(func_decl* q) { m_query_pred = q; }

        void set_unsat() { m_last_result = l_false; }

        void set_model_converter(model_converter_ref& mc) { m_mc = mc; }

        void get_rules_along_trace (datalog::rule_ref_vector& rules);

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
    };

};

#endif
