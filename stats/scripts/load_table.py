#!/usr/bin/python

import sys
import csv
import sqlite3 as sql

from optparse import OptionParser

fld_dict = {'ufo.expand': 'expand', 'ufo.post': 'post', 
            'Invariant.add': 'inv_add', 
            'refiner.nnf': 'ref_nff', 'z3.to_expr': 'to_z3', 
            'refiner.mkInScope.elim_and_simplify': 'ref_inscope_eas', 
            'refiner.total': 'ref_total', 'Status': 'status', 
            'ufo.expand.is_covered': 'expand_iscover', 
            'refiner.mkInScope.elim_node': 'ref_inscope_enode', 
            'aArg.size': 'argsz', 'refiner.assumptcaions': 'ref_asm', 
            'msat.from_expr': 'from_msat', 
            'refiner.mkInScope.variants': 'ref_inscope_var', 
            'refiner.pre': 'ref_pre', 'refiner.interps': 'ref_iterp', 
            'refiner.mkInScope.out_of_scope': 'ref_inscope_out', 
            'ufo.main_loop': 'loop', 
            'refiner.mkInScope.elim_other': 'ref_inscope_eother', 
            'refiner.mkInScope.z3.forall': 'ref_inscope_forall', 
            'Cpu': 'cpu', 'refiner.mkInScope.propSimp': 'ref_inscope_simp', 
            'z3.from_expr': 'from_z3', 'msat.to_expr': 'to_msat', 
            'refiner.assumptions.total': 'ref_asm_total', 
            'ufo.total': 'total', 'refiner.mkInScope': 'ref_inscope', 
            'Result': 'res', 'File': 'file', 
            'asm_refiner.simplify.assumptions': 'asm_ref'}

def fld_name (fld):
    if fld in fld_dict: return fld_dict [fld]
    return fld.replace ('.', '_')

def get_type (v):
    if v == None: return None
    if v == '': return None
    try:
        int (v)
        return 'integer'
    except ValueError:
        try:
            float (v)
            return 'real'
        except ValueError:
            return 'text'
    
def deduce_types (reader):
    types = map (get_type, next (reader))
    def merge_type (t1, t2):
        if t1 == 'text' or t2 == 'text': return 'text'
        elif t1 == 'real' or t2 == 'real': return 'real'
        elif t1 == 'integer' or t2 == 'integer': return 'integer'
        else: 
            assert t1 == t2 == None
            return None

    for row in reader:
        types = [merge_type (t, get_type (i)) for (t, i) in zip (types, row)]
    return types
    

def create_ufo_table (db, table, flds, types):
    sql_fld_names = map (fld_name, flds)
    sql_fld_types = map (lambda x: x == None and 'text' or x, types)

    sql_col_def = ', '.join ([' '.join ((x, y)) 
                             for (x,y) in zip (sql_fld_names, sql_fld_types)])
    
    print "Creating table '{table}'".format(table=table)

    old_sql_cols = """
                                file text,
                                status integer, 
	      	     	        res text, 
                                cpu real, 
				total real,
				argsz integer,
				loop integer,
				inv_add real,
				asm_ref real,
				from_msat real,
				to_msat real,
				ref_asm real, 
				ref_asm_total real,
				ref_iterp real,
				ref_inscope real,
				ref_inscope_eas real,
				ref_inscope_enode real,
				ref_inscope_eother real,
				ref_inscope_out real,
				ref_inscope_simp real,
				ref_inscope_var real,
				ref_inscope_forall real,
				ref_nff real,
				ref_pre real,
				ref_total real,
				expand real,
				expand_iscover real,
				post real,
				from_z3 real,
				to_z3 real
"""
    ctable = """
drop table if exists {name};
drop index if exists {name}_total;
drop index if exists {name}_file;
create	table if not exists {name}( {cols} );

create unique index if not exists {name}_file on {name}(file);

"""
    ctable = ctable.format (name=table, cols=sql_col_def)
    db.cursor ().executescript (ctable);
    db.commit ()
    
def load_ufo_csv (csvfile, db, table, create_table = False):
    print "Loading file '{name}'".format (name=csvfile)
    c = db.cursor ()
    with open (csvfile, 'rb') as infile:
        reader = csv.reader (infile, dialect='excel')
        # read the header
        fld = next (reader)
        
        col = ', '.join (['?' for i in fld])
        ivalue = "insert into {name} values ({col});"
        ivalue = ivalue.format (name=table, col=col)
        
        if create_table: 
            types = deduce_types (reader)
            create_ufo_table (db, table, fld, types)

            ## reset everything to the beginning
            infile.seek (0)
            reader = csv.reader (infile, dialect='excel')
            next (reader)

        c.executemany (ivalue, reader)
    db.commit ()
    
def create_solved_views (db, table):
    print "Creating solved views"
    view = """
create view if not exists {name}_solved as select num, count(*) as solved from {name}, nums where (res is 'SAFE' or res is 'CEX') and total <= num group by num order by num;

create view if not exists {name}_solved_safe as select num, count(*) as solved from {name}, nums where (res is 'SAFE') and total <= num group by num order by num;

create view if not exists {name}_solved_cex as select num, count(*) as solved from {name}, nums where (res is 'CEX') and total <= num group by num order by num;

""".format (name=table)

    db.cursor ().executescript (view)
    db.commit ()

def parseOpt ():
    parser = OptionParser ()
    parser.add_option ("-t", "--table", dest="table",
                       help="Table name", metavar="TABLE");
    parser.add_option ("--use-existing", action="store_true", dest="existing", 
                       default = False, help = "Do not re-create the table")
    parser.add_option ("--db", dest="db", 
                       help="Database location",
                       default="results.db")

    (options, args) = parser.parse_args ()

    if len (args) < 1:
        parser.error ("no file given")

    if options.table == None:
        parser.error ("no table name")

    return (options, args)
    
    
def main ():

    (opt, args) = parseOpt ()
    db = sql.connect (opt.db)
    create_table = not opt.existing
    for file in args:
        load_ufo_csv (file, db, opt.table, create_table)
        create_table = False

#    create_solved_views (db, opt.table)
    
    db.close ()


if __name__ == "__main__":
    sys.exit (main ())
