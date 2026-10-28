module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner.NoncentralChecks
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner.Coverage

/-!
# The noncentral J₂ involution centralizer as E₄ × A₅

The sixty checked words define an A₅ homomorphism. Four central words define
an E₄ homomorphism, and the checked commutation identities give their product
homomorphism into the literal centralizer of the standard generator a.
The exhaustive 240-word cover proves surjectivity. Evaluation at the faithful
pair (0,1) proves that the kernel is trivial, giving the required isomorphism
of the whole centralizer rather than merely a section or quotient.

Source: Aschbacher–Smith 16.1.5(8), printed p.1172. All elements are words in
the retained degree-100 ATLAS carrier, and all table identities are kernel checked.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
open NoncentralData

private def centralWord (i : Fin 240) : Subgroup.centralizer ({a} : Set Carrier) :=
  ⟨conjugator i, Subgroup.mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp (conjugator_centralizes i))⟩

private theorem centralWord_val (i : Fin 240) :
    inclusion (centralWord i).val = conjugatorTable i := conjugator_inclusion i

private theorem centralWord_mul_point (i j : Fin 240) (p : Fin 100) :
    inclusion (centralWord i * centralWord j).val p =
      (conjugatorTable i * conjugatorTable j) p := by
  change inclusion ((centralWord i).val * (centralWord j).val) p = _
  rw [map_mul, centralWord_val, centralWord_val]

private theorem centralWord_mul (i j k : Fin 240)
    (h : conjugatorTable k 0 = (conjugatorTable i * conjugatorTable j) 0 ∧
      conjugatorTable k 1 = (conjugatorTable i * conjugatorTable j) 1) :
    centralWord k = centralWord i * centralWord j := by
  apply a_centralizer_ext
  · rw [centralWord_val, centralWord_mul_point]
    exact h.1
  · rw [centralWord_val, centralWord_mul_point]
    exact h.2

private noncomputable def simpleHom : A5 →* Subgroup.centralizer ({a} : Set Carrier) :=
  MonoidHom.mk' (fun x => centralWord (simpleIndex (simpleEquiv.symm x))) (by
    intro x y
    have hm := simpleEnum_mul (simpleEquiv.symm x) (simpleEquiv.symm y)
    change simpleEquiv _ = simpleEquiv _ * simpleEquiv _ at hm
    rw [simpleEquiv.apply_symm_apply, simpleEquiv.apply_symm_apply] at hm
    have hi := congrArg simpleEquiv.symm hm
    rw [simpleEquiv.symm_apply_apply] at hi
    rw [← hi]
    exact centralWord_mul _ _ _ (simpleTable_mul _ _))

private def centerHom : E4 →* Subgroup.centralizer ({a} : Set Carrier) :=
  MonoidHom.mk' (fun x => centralWord (centerIndex x)) (by
    intro x y
    exact centralWord_mul _ _ _ (centerTable_mul x y))

private theorem homs_commute (x : E4) (y : A5) : Commute (centerHom x) (simpleHom y) := by
  change centralWord (centerIndex x) * centralWord (simpleIndex (simpleEquiv.symm y)) =
    centralWord (simpleIndex (simpleEquiv.symm y)) * centralWord (centerIndex x)
  apply a_centralizer_ext
  · rw [centralWord_mul_point, centralWord_mul_point]
    exact (factors_commute x (simpleEquiv.symm y)).1
  · rw [centralWord_mul_point, centralWord_mul_point]
    exact (factors_commute x (simpleEquiv.symm y)).2

private noncomputable def productHom : E4 × A5 →*
    Subgroup.centralizer ({a} : Set Carrier) :=
  MonoidHom.noncommCoprod centerHom simpleHom homs_commute

private theorem productHom_surjective : Function.Surjective productHom := by
  intro g
  obtain ⟨i, hi⟩ := a_centralizer_cover g.val g.property
  refine ⟨(factorCenter i, simpleEquiv (factorSimple i)), ?_⟩
  change centralWord (centerIndex (factorCenter i)) *
    centralWord (simpleIndex (simpleEquiv.symm (simpleEquiv (factorSimple i)))) = g
  rw [simpleEquiv.symm_apply_apply]
  have hprod := centralWord_mul (centerIndex (factorCenter i))
    (simpleIndex (factorSimple i)) i ⟨(product_cover i).1.symm, (product_cover i).2.symm⟩
  rw [← hprod]
  exact Subtype.ext hi.symm

private theorem productHom_injective : Function.Injective productHom := by
  apply (MonoidHom.ker_eq_bot_iff productHom).mp
  apply (Subgroup.eq_bot_iff_forall productHom.ker).mpr
  rintro ⟨x, y⟩ h
  change productHom (x, y) = 1 at h
  have hp := congrArg (fun g : Subgroup.centralizer ({a} : Set Carrier) => inclusion g.val) h
  change inclusion ((centralWord (centerIndex x)).val *
    (centralWord (simpleIndex (simpleEquiv.symm y))).val) = inclusion 1 at hp
  rw [map_mul, centralWord_val, centralWord_val, map_one] at hp
  obtain ⟨hx, hi⟩ := product_kernel x (simpleEquiv.symm y)
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 0) hp)
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 1) hp)
  apply Prod.ext hx
  have hy := congrArg simpleEquiv hi
  rw [simpleEquiv.apply_symm_apply] at hy
  exact hy.trans simpleEnum_zero

/-- The entire noncentral representative centralizer is the actual direct product E₄ × A₅. -/
noncomputable def a_centralizer_equiv :
    Subgroup.centralizer ({a} : Set Carrier) ≃* E4 × A5 :=
  (MulEquiv.ofBijective productHom ⟨productHom_injective, productHom_surjective⟩).symm

/-- The simple factor retains its concrete embedding by the checked carrier words. -/
theorem a_centralizer_equiv_symm_simple (i : Fin 60) :
    (a_centralizer_equiv.symm (1, simpleEquiv i)).val =
      conjugator (simpleIndex i) := by
  change (centerHom 1 * simpleHom (simpleEquiv i)).val = _
  rw [map_one, one_mul]
  change (centralWord (simpleIndex (simpleEquiv.symm (simpleEquiv i)))).val = _
  rw [simpleEquiv.symm_apply_apply]
  rfl

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
