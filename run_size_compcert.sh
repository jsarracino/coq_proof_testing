#!/usr/bin/env sh

./proof_size.py --prelude CompCert/   \
  lib/Axioms.v lib/Coqlib.v driver/Compopts.v MenhirLib/Alphabet.v cparser/Cabs.v MenhirLib/Grammar.v MenhirLib/Validator_classes.v flocq/Core/Raux.v flocq/Core/Digits.v lib/Intv.v lib/Maps.v lib/Zbits.v lib/Iteration.v lib/UnionFind.v lib/FSetAVLplus.v lib/IntvSets.v lib/Decidableplus.v lib/BoolEqual.v common/Errors.v MenhirLib/Automaton.v flocq/Core/Defs.v lib/Lattice.v lib/Postorder.v common/Unityping.v MenhirLib/Validator_safe.v flocq/Core/Float_prop.v flocq/Core/Round_pred.v MenhirLib/Interpreter.v flocq/Calc/Bracket.v flocq/Calc/Operations.v flocq/Core/Generic_fmt.v MenhirLib/Interpreter_complete.v MenhirLib/Interpreter_correct.v flocq/Calc/Div.v flocq/Core/Ulp.v flocq/Prop/Sterbenz.v flocq/Calc/Sqrt.v MenhirLib/Main.v flocq/Core/Round_NE.v cparser/Parser.v flocq/Core/FIX.v flocq/Core/FLX.v flocq/Core/FLT.v flocq/Core/FTZ.v flocq/Core/Core.v flocq/Prop/Relative.v flocq/Prop/Double_rounding.v flocq/Prop/Round_odd.v flocq/Calc/Plus.v flocq/IEEE754/BinarySingleNaN.v flocq/Prop/Plus_error.v flocq/Prop/Div_sqrt_error.v flocq/IEEE754/Binary.v flocq/IEEE754/Bits.v lib/IEEE754_extra.v x86_64/Archi.v lib/Integers.v lib/Floats.v lib/Ordered.v lib/Heaps.v common/AST.v common/Linking.v common/Values.v cfrontend/Ctypes.v common/Switch.v backend/Registers.v common/Memdata.v common/Memtype.v common/Builtins0.v common/Memory.v x86/Builtins1.v common/Builtins.v backend/Kildall.v common/Events.v cfrontend/Csyntax.v cfrontend/Initializers.v common/Smallstep.v common/Separation.v x86/Op.v backend/Cminor.v common/Behaviors.v cfrontend/Csem.v cfrontend/Clight.v cfrontend/SimplExpr.v cfrontend/ClightBigstep.v cfrontend/Ctyping.v cfrontend/Cstrategy.v cfrontend/Initializersproof.v common/Determinism.v cfrontend/SimplExprspec.v backend/Cminortyping.v cfrontend/Csharpminor.v cfrontend/Cminorgen.v cfrontend/Cminorgenproof.v cfrontend/Cexec.v cfrontend/SimplExprproof.v backend/CminorSel.v x86/Machregs.v x86/SelectOp.v backend/RTLgen.v backend/Inlining.v backend/Renumber.v backend/Liveness.v backend/ValueDomain.v backend/CSEdomain.v backend/Unusedglob.v backend/Inliningspec.v backend/Renumberproof.v backend/RTLgenspec.v x86/CombineOp.v backend/Unusedglobproof.v x86/Conventions1.v backend/Conventions.v cfrontend/SimplLocals.v cfrontend/Cshmgen.v backend/SplitLong.v backend/Tailcall.v backend/Inliningproof.v backend/RTLtyping.v backend/LTL.v cfrontend/SimplLocalsproof.v cfrontend/Cshmgenproof.v x86/SelectLong.v backend/Tailcallproof.v x86/CombineOpproof.v backend/Allocation.v backend/Tunneling.v backend/Linear.v backend/SplitLongproof.v backend/RTLgenproof.v backend/Lineartyping.v backend/Linearize.v backend/CleanupLabels.v backend/Debugvar.v backend/Bounds.v backend/SelectDiv.v backend/Allocproof.v backend/Tunnelingproof.v backend/Linearizeproof.v backend/CleanupLabelsproof.v backend/Debugvarproof.v x86/Stacklayout.v backend/Selection.v x86/ValueAOp.v backend/NeedDomain.v backend/Mach.v x86/Asm.v x86/SelectLongproof.v backend/Stacking.v x86/Asmgen.v backend/ValueAnalysis.v x86/ConstpropOp.v backend/Stackingproof.v x86/NeedOp.v backend/Asmgenproof0.v backend/SelectDivproof.v x86/Asmgenproof1.v backend/Constprop.v backend/CSE.v x86/ConstpropOpproof.v backend/Deadcode.v backend/CSEproof.v backend/Deadcodeproof.v  backend/Constpropproof.v x86/Asmgenproof.v driver/Compiler.v driver/Complements.v \
  common/Globalenvs.v lib/Parmov.v x86/SelectOpproof.v backend/Selectionproof.v flocq/Core/Zaux.v flocq/Calc/Round.v backend/Locations.v cfrontend/Cop.v backend/RTL.v MenhirLib/Validator_complete.v flocq/Prop/Mult_error.v lib/Wfsimpl.v 
  # The above line are training files for proverbot, omit if needed