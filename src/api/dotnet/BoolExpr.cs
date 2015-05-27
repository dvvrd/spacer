/*++
Copyright (<c>) 2012 Microsoft Corporation

Module Name:

    BoolExpr.cs

Abstract:

    Z3 Managed API: Boolean Expressions

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Boolean expressions
    /// </summary>
    public class BoolExpr : Expr
    {
        #region Internal
        /// <summary> Constructor for BoolExpr </summary>
        internal BoolExpr(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }
        #endregion

        /// <summary>
        /// Translates (copies) the boolean term to the Context <paramref name="ctx"/>.
        /// </summary>
        /// <param name="ctx">A context</param>
        /// <returns>A copy of the boolean term which is associated with <paramref name="ctx"/></returns>
        new public BoolExpr Translate(Context ctx)
        {
            Contract.Requires(ctx != null);
            Contract.Ensures(Contract.Result<BoolExpr>() != null);

            if (ReferenceEquals(Context, ctx))
                return this;
            else
                return new BoolExpr(ctx, Native.Z3_translate(Context.nCtx, NativeObject, ctx.nCtx));
        }
    }
}
