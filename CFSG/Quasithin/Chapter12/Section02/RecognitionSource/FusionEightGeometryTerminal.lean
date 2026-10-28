module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryDecompositionPointGeometry
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAlternatingEightGeometryOrbits
public import Theory.Representation.BinaryPermutation.EightPointSylowParity
public import Theory.GroupTheory.ConjugateSupplementIntersection

/-!
# The corrected terminal A₈ fusion argument

Let E = Ω₁Z(C_T(v)), U = C_V(C_T(v)), and B = C_E(L). Assume the
corrected decomposition E = U B and that T centralizes B. The original
fixed-line theorem identifies U ∩ B with ⟨z⟩. Known-simple uniqueness
makes B and its actual g-conjugate disjoint. The abelian product-order
formula then forces |U ∩ Uᵍ| > 2.

On the other hand, the marked quotient maps the point-component Sylow
to a Sylow of the weight-two stabilizer in A₈. Pair parity on its fixed
words, together with the established outside-fusion orbit calculation,
is a homomorphism U ∩ Uᵍ → C₂ with trivial kernel. Thus this intersection
has order at most two, a contradiction. This works with the entire
point-fixed core and needs neither its exact dimension nor the printed
hyperplane identity.

The omega-center containment and its actual `false_of_omega_le` consumer
retain precisely the two supplied geometric premises. Their source
construction remains with the point-span decomposition and omega-center
assembly owners. Source: Aschbacher--Smith 12.2.16, printed p.800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open BinaryPermutation
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
namespace AlternatingEightFusion
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable (C : AlternatingEightFusion T L V)

/-- The two literal fixed subgroups intersect in the original constant line. -/
theorem pointCore_inf_pointFixed_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Nat.card (C.pointCore ⊓ C.pointFixed : Subgroup G) = 2 := by
  let := D.elementary
  have hzE := C.fixed_mem_pointSylow_omega h D structural
  have hzU : (C.z : G) ∈ C.pointCore := by
    rw [C.pointCore_eq_inf_omega D]
    exact ⟨C.z.property, hzE⟩
  have he : C.pointCore ⊓ C.pointFixed = zpowers (C.z : G) := by
    apply le_antisymm
    · intro x hx
      rcases C.fixed_line x hx.1.1 hx.2.2 with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · exact zpowers_le.mpr ⟨hzU, hzE, C.z_fixed⟩
  rw [he, Nat.card_zpowers]
  exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ C.z.property) C.z_ne

/-- Outside fusion and pair parity bound the actual conjugate intersection. -/
theorem pointCore_intersection_card_le_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (hnone : NoEscape L V) :
    Nat.card (C.pointCore ⊓ C.pointCore.map (MulAut.conj C.g).toMonoidHom :
      Subgroup G) ≤ 2 := by
  let A : AlternatingEightCoreCoordinates L V :=
    ⟨C.groupEquiv, C.vectorEquiv, C.intertwines⟩
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    apply (((structural G T L h).2.2 V D).2.2.2).resolve_right
    intro he
    exact C.z_ne (mem_bot.mp (he ▸
      (show (C.z : G) ∈ V ⊓ centralizer (L : Set G) from ⟨C.z.property,C.z_fixed⟩)))
  obtain ⟨P,hP⟩ := C.pointComponentImage_is_sylow hnone
  obtain ⟨f,hf⟩ := EightPointSylowParity.exists_weight_parity
    (C.vectorEquiv C.v).toAdd.val C.weight_two P
  let H := C.pointCore ⊓ C.pointCore.map (MulAut.conj C.g).toMonoidHom
  have hHV : H ≤ V := inf_le_left.trans inf_le_left
  let q : H →* Multiplicative (ZMod 2) :=
    ((f.comp (core (Fin 8)).subtype).toAddMonoidHom.toMultiplicative).comp
      (C.vectorEquiv.toMonoidHom.comp (Subgroup.inclusion hHV))
  have hodd (x : H) (hx : (x : G) ≠ 1) :
      f (C.vectorEquiv ⟨x,hHV x.property⟩).toAdd.val = 1 := by
    have hxg := x.property.2
    obtain ⟨y,hy,he⟩ := hxg
    have hy1 : y ≠ 1 := by
      intro hy1
      exact hx (he.symm.trans (by rw [hy1, map_one]))
    have hw := A.outside_weights h D structural hnone hMV
      ⟨y,hy.1⟩ ⟨x,hHV x.property⟩ hy1 C.outside he
    apply hf _ ?_ (hw.elim (fun hh => Or.inr hh.2) (fun hh => Or.inl hh.2))
    rw [hP]
    rintro ⟨a,ha⟩
    obtain ⟨l,hl,rfl⟩ := ha
    have hc : (l : G) ∈ centralizer ({(x : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr (x.property.1.2 l hl)
    exact congrArg (fun w : core (Fin 8) => w.val)
      ((C.componentProjection_fixes_iff l ⟨x,hHV x.property⟩).mpr hc)
  have hq : Function.Injective q := by
    apply (injective_iff_map_eq_one q).mpr
    intro x hx
    by_contra hn
    have ho := hodd x (fun he => hn (Subtype.ext he))
    have hz : f (C.vectorEquiv ⟨x,hHV x.property⟩).toAdd.val = 0 :=
      congrArg Multiplicative.toAdd hx
    exact one_ne_zero (ho.symm.trans hz)
  have hc := Nat.card_le_card_of_injective q hq
  simpa only [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] using hc

/-- The corrected supplement and its T-centralization imply the requested containment. -/
theorem omega_le_of_pointCore_decomposition
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (hnone : NoEscape L V)
    (hsplit : omegaCenterIn C.pointSylow = C.pointCore ⊔ C.pointFixed)
    (hT : C.pointFixed ≤ centralizer ((T : Subgroup G) : Set G)) :
    omegaCenterIn C.pointSylow ≤ V := by
  have hlo := two_lt_card_inf_conjugate_of_disjoint_supplement
    (omegaCenterIn C.pointSylow) C.pointCore C.pointFixed
    (C.pointCore_le_omega D) inf_le_left hsplit
    (C.pointCore_inf_pointFixed_card h D structural) C.g
    (normalizer_le_normalizer_omegaCenterIn C.pointSylow C.normalizes)
    (C.pointFixed_disjoint_conjugate h structural hT)
  exact (not_lt_of_ge (C.pointCore_intersection_card_le_two h D structural hnone) hlo).elim

/-- Apply the containment to the original fixed-line omega-center endpoint. -/
theorem false_of_pointCore_decomposition
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (hnone : NoEscape L V)
    (hsplit : omegaCenterIn C.pointSylow = C.pointCore ⊔ C.pointFixed)
    (hT : C.pointFixed ≤ centralizer ((T : Subgroup G) : Set G)) : False := by
  exact C.false_of_omega_le h D structural hnone
    (C.omega_le_of_pointCore_decomposition h D structural hnone hsplit hT)

end AlternatingEightFusion
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
