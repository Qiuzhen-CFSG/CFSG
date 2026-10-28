module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.BModel

/-!
# Counting the native B classes

A bounded sixty-four-flag and sixteen-parameter certificate counts the allowed unions of the marked classes. No wreath conjugator search is used.

Source: Aschbacher–Smith 13.9.4–5, printed p.970.
-/

@[expose] public section
namespace SymmetricFourWreath.InvolutionClasses

def classFlagCard (b:Fin 6→Bool) : Nat :=
  Fintype.card {a:Parameters // a≠1 ∧ b (parameterIndex a)=true}

theorem classFlagCard_eq : ∀b:Fin 6→Bool,
    classFlagCard b=(if b 0 then 1 else 0)+(if b 1 then 2 else 0)+
      (if b 2 then 4 else 0)+(if b 3 then 4 else 0)+(if b 4 then 4 else 0) := by
  decide +kernel

theorem classFlagCard_nine (b:Fin 6→Bool)
    (h0:b 0=true) (h1:b 1=false) (h2:b 2=false)
    (hn1:classFlagCard b≠1) (hn5:classFlagCard b≠5) :
    classFlagCard b=9 ∧ b 3=true ∧ b 4=true := by
  have he := classFlagCard_eq b
  cases h3:b 3 <;> cases h4:b 4 <;> simp_all
end SymmetricFourWreath.InvolutionClasses
