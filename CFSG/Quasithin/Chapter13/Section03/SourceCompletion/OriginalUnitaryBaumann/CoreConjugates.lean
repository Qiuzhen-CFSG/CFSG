module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.ConjugateImages
public import Theory.Representation.G2BinaryRootLift

/-!
# Two conjugates of the original elementary product core

Write Q = V C with C central in the Baumann group B, and Q = C_B(V).
A conjugate of V contained in Q has the same centralizer Q. Every other
conjugate has the marked root-eight image. Its elementary centralizer is
self-centralizing and has that same image. The long-root fixed-space
detector and the unique-lift theorem therefore identify all moving core
conjugates. Thus Q has at most two conjugates under N_G(B).

OriginalUnitaryNoncentrality.BaumannEndpoint applies the Sylow stabilizer
argument to this orbit, retaining the original embedded core throughout.
Source: Aschbacher--Smith B.2.21 and 13.3.10(2), printed pp.82--83,888.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G]

/-- The elementary product core has at most two conjugates under the
Baumann normalizer, with the second one supplied by the original escape. -/
theorem unitary_baumann_core_conjugates
    (V B Q C : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 Q]
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hBN : B ≤ normalizer (V : Set G))
    (himage : (inducedAutomizer V B).map rho = Atlas.G2.BinaryCore.elementary)
    (hcore : Q = B ⊓ centralizer (V : Set G)) (hprod : Q = V ⊔ C)
    (hC : C ≤ centralizer (B : Set G))
    (x : G) (hx : x ∈ normalizer (B : Set G)) (hext : ¬ V.conjBy x ≤ Q) :
    ∀ g ∈ normalizer (B : Set G), Q.conjBy g = Q ∨ Q.conjBy g = Q.conjBy x := by
  have hQB : Q ≤ B := hcore.le.trans inf_le_left
  have hVQ : V ≤ Q := hprod ▸ le_sup_left
  have hVB := hVQ.trans hQB
  have hCB : C ≤ B := (hprod ▸ le_sup_right).trans hQB
  let U := V.subgroupOf B
  let Q₀ := Q.subgroupOf B
  let C₀ := C.subgroupOf B
  let : U.Normal := normal_subgroupOf_of_le_normalizer hBN
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVB (p := 2)
  let : IsElementaryAbelian 2 Q₀ := IsElementaryAbelian.subgroupOf hQB (p := 2)
  let EUa := (subgroupOfEquivOfLe hVB).toAdditive
  let EU : Additive U ≃ₗ[F] Additive V := { EUa with map_smul' := ZMod.map_smul EUa }
  let E' := EU.trans E
  let q : B →* Atlas.G2.Model F :=
    (rho.comp V.normalizerMonoidHom.rangeRestrict).comp (inclusion hBN)
  have he' (b : B) (v : U) :
      E' (Additive.ofMul (MulAut.conjNormal b v)) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (q b) (E' (Additive.ofMul v)) :=
    he (V.normalizerMonoidHom.rangeRestrict (inclusion hBN b)) (EU (Additive.ofMul v))
  have hk : q.ker = Q₀ := by
    rw [unitary_coordinate_kernel U q E' he']
    ext b
    change b ∈ centralizer (U : Set B) ↔ (b : G) ∈ Q
    rw [hcore]
    constructor
    · intro hb
      refine ⟨b.property,?_⟩
      intro v hv
      exact congrArg Subtype.val (hb ⟨v,hVB hv⟩ hv)
    · intro hb v hv
      exact Subtype.ext (hb.2 v hv)
  have hprod' : Q₀ = U ⊔ C₀ := by
    change Q.subgroupOf B = V.subgroupOf B ⊔ C.subgroupOf B
    rw [←subgroupOf_sup hVB hCB,←hprod]
  have hC' : C₀ ≤ center B := by
    intro c hc
    rw [mem_center_iff]
    intro b
    exact Subtype.ext (hC hc b b.property)
  have hmap (A : Subgroup G) (hAB : A ≤ B) :
      (A.subgroupOf B).map q = (inducedAutomizer V A).map rho := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨_,⟨⟨b,hBN b.property⟩,hb,rfl⟩,rfl⟩
    · rintro ⟨_,⟨n,hnA,rfl⟩,rfl⟩
      exact ⟨⟨n.val,hAB hnA⟩,hnA,rfl⟩
  have hdata (a : G) (ha : a ∈ normalizer (B : Set G)) :
      Q.conjBy a ≤ B ∧ V.conjBy a ≤ Q.conjBy a ∧
      Q.conjBy a = B ⊓ centralizer (V.conjBy a : Set G) := by
    have hBa : B.map (MulAut.conj a).toMonoidHom = B :=
      mem_normalizer_iff_map_conj_eq.mp ha
    refine ⟨(map_mono hQB).trans_eq hBa,map_mono hVQ,?_⟩
    change Q.map (MulAut.conj a).toMonoidHom = _
    rw [hcore,map_inf _ _ _ (MulAut.conj a).injective,hBa,map_centralizer_equiv]
    rfl
  have hself (a : G) (ha : a ∈ normalizer (B : Set G)) :
      centralizer ((Q.conjBy a).subgroupOf B : Set B) ≤ (Q.conjBy a).subgroupOf B := by
    intro b hb
    apply (hdata a ha).2.2.ge
    refine ⟨b.property,?_⟩
    intro v hv
    have hvQ := (hdata a ha).2.1 hv
    exact congrArg Subtype.val (hb ⟨v,(hdata a ha).1 hvQ⟩ hvQ)
  have hp : (inducedAutomizer V B).map rho ≤ Atlas.G2.LieParabolicSetup.radical₂ := by
    rw [himage]
    rintro _ ⟨t,ht,rfl⟩
    exact ⟨Atlas.G2.BinaryCore.parameters t,by simpa [Atlas.G2.BinaryCore.parameters] using ht.2,rfl⟩
  have him (a : G) (ha : a ∈ normalizer (B : Set G)) (hne : ¬ V.conjBy a ≤ Q) :
      ((Q.conjBy a).subgroupOf B).map q = Atlas.G2.BinaryCore.elementary := by
    have hn : ¬ V.conjBy a ≤ centralizer (V : Set G) := by
      intro hh
      exact hne ((le_inf ((hdata a ha).2.1.trans (hdata a ha).1) hh).trans hcore.ge)
    have hv := unitary_baumann_moving_conjugate_image V B rho E he hVB hBN hp
      a⁻¹ ((normalizer _).inv_mem ha) (by simpa only [inv_inv,conjBy] using hn)
    simp only [inv_inv] at hv
    rw [hmap _ (hdata a ha).1]
    apply le_antisymm
    · exact (map_mono (map_mono (subgroupOf_mono _ (hdata a ha).1))).trans_eq himage
    · rw [←hv]
      exact map_mono (map_mono (subgroupOf_mono _ (hdata a ha).2.1))
  intro g hg
  by_cases hgV : V.conjBy g ≤ Q
  · left
    have hQQg : Q ≤ Q.conjBy g := by
      rw [(hdata g hg).2.2]
      exact le_inf hQB ((le_centralizer Q).trans (centralizer_le hgV))
    apply (eq_of_le_of_card_ge hQQg ?_).symm
    exact (card_map_of_injective (MulAut.conj g).injective).le
  · right
    let A := (Q.conjBy x).subgroupOf B
    let D := (Q.conjBy g).subgroupOf B
    let : IsElementaryAbelian 2 (Q.conjBy x) := IsElementaryAbelian.map (MulAut.conj x).toMonoidHom
    let : IsElementaryAbelian 2 (Q.conjBy g) := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf (hdata x hx).1
    let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf (hdata g hg).1
    have hh := root_eight_lift_unique U Q₀ C₀ A D q E' he' hk hprod' hC'
      (hself x hx) (hself g hg) (him x hx hext) (him g hg hgV)
    have hm := congrArg (map B.subtype) hh
    simpa only [A,D,map_subgroupOf_eq_of_le (hdata x hx).1,
      map_subgroupOf_eq_of_le (hdata g hg).1] using hm
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
