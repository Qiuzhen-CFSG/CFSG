module

public import Theory.Frattini.ConjugateCentralFactors

/-!
# Disjoint fixed factors force an elementary core

Suppose Q=C_S(U), Q=UD with U central elementary in Q, D centralizing Uᵉ,
and S=UᵉQ is preserved by e. Both Q and Qᵉ are central elementary
supplements of their intersection, so their embedded Frattini subgroups
coincide. If Φ(Q) lies in C and C intersects Cᵉ trivially, then Φ(Q)=1.

This packages the conjugate-central-factor theorem for the geometry in
Aschbacher–Smith 3.3.31, printed p.602, without requiring the subsequent
classification of its cyclic and elementary-four fixed factors.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem elementary_of_conjugate_central_factors_disjoint
    (S U Q D C : Subgroup G) (e : G ≃* G)
    (hSmap : S.map e.toMonoidHom = S)
    (hcore : Q = S ⊓ centralizer (U : Set G)) (hprod : Q = U ⊔ D)
    (hcentralizes : D ≤ centralizer (U.map e.toMonoidHom : Set G))
    (hspan : S = U.map e.toMonoidHom ⊔ Q)
    (hU : IsElementaryAbelian 2 U) (hQtwo : IsPGroup 2 Q)
    (hSQ : S ≤ normalizer (Q : Set G))
    (hphi : (frattini Q).map Q.subtype ≤ C)
    (hdisjoint : C ⊓ C.map e.toMonoidHom = ⊥) :
    IsElementaryAbelian 2 Q := by
  have hi := frattini_conjugate_central_factors S U Q D e hSmap hcore hprod
    hcentralizes hspan hU hQtwo hSQ
  have he := frattini_map_eq_of_central_elementary_supplement Q D U hQtwo hU
    (le_centralizer_iff.mp (hcore ▸ inf_le_right)) hprod
  rw [← he] at hi
  have hb : (frattini Q).map Q.subtype = ⊥ := by
    apply bot_unique
    apply le_trans _ hdisjoint.le
    apply le_inf hphi
    rw [← hi]
    exact map_mono hphi
  let : Fact (IsPGroup 2 Q) := ⟨hQtwo⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    (((frattini Q).map_eq_bot_iff_of_injective Q.subtype_injective).mp hb)
end Subgroup
