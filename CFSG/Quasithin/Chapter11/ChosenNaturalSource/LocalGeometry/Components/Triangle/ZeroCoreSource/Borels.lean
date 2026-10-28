module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.Endpoints
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.AmbientQuotient
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups

/-!
# The original triangle Borels

In an A5 two-core quotient, the local Sylow has index three in its
normalizer. The original Cartan cubic therefore supplements that Sylow
in the full local Borel. Apply this with the actual S₀ intersections,
using the original PSL₃/PGL₃ marking to identify X ∩ K₀ = X ∩ L₁.
The Cartan splitting supplies the other cubic. No quotient kernel is
removed, and the resulting Borels are the literal subgroup normalizers.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed p.762, the verification of Hypothesis F.1.1.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
open ChapterF.Source

private theorem a5_sylow_borel_index {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 5)) (P : Sylow 2 H) :
    (P : Subgroup H).relIndex (normalizer (P : Set H)) = 3 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ x ∈ pCore 2 H
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hkP : q.ker ≤ (P : Subgroup H) := by
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal P
  let Q := P.mapSurjective hq
  have hN : (normalizer (Q : Set (alternatingGroup (Fin 5)))).index = 5 := by
    obtain ⟨i, hi⟩ :=
      Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer Q
    have hc : Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) i) = 12 := by
      rw [Nat.card_eq_fintype_card]
      clear Q hi
      revert i
      decide +kernel
    have hm := (MulAction.stabilizer (alternatingGroup (Fin 5)) i).index_mul_card
    rw [hc, nat_card_alternatingGroup] at hm
    norm_num [Nat.factorial] at hm
    rw [hi]
    omega
  have hP : (Q : Subgroup (alternatingGroup (Fin 5))).index = 15 := by
    have hc : Nat.card Q = 4 := by
      rw [Q.card_eq_multiplicity, nat_card_alternatingGroup, Nat.card_fin]
      decide +kernel
    have hm := (Q : Subgroup (alternatingGroup (Fin 5))).index_mul_card
    rw [hc, nat_card_alternatingGroup] at hm
    norm_num [Nat.factorial] at hm
    omega
  have he := relIndex_mul_index (Q : Subgroup (alternatingGroup (Fin 5))).le_normalizer
  change (Q : Subgroup (alternatingGroup (Fin 5))).relIndex
    (normalizer (Q : Set (alternatingGroup (Fin 5)))) *
    (normalizer (Q : Set (alternatingGroup (Fin 5)))).index = _ at he
  rw [hN,hP] at he
  have hmap := relIndex_map_map q (P : Subgroup H) (normalizer (P : Set H))
  have hkN : q.ker ≤ normalizer (P : Set H) :=
    hkP.trans (P : Subgroup H).le_normalizer
  rw [sup_eq_left.mpr hkP,sup_eq_left.mpr hkN,
    P.normalizer_map_surjective q hq] at hmap
  change (Q : Subgroup (alternatingGroup (Fin 5))).relIndex
    (normalizer (Q : Set (alternatingGroup (Fin 5)))) = _ at hmap
  omega

/-- The original Cartan cubic supplements the local Sylow in its full Borel. -/
theorem borel_eq_sylow_sup_cubic {G : Type*} [Group G] [Finite G]
    {B U C : Subgroup G} (P : Sylow 2 B)
    (hP : (P : Subgroup B).map B.subtype = U ⊓ B)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hCB : C ≤ B) (hCN : C ≤ normalizer ((U ⊓ B : Subgroup G) : Set G))
    (hC : Nat.card C = 3) : borel B U = (U ⊓ B) ⊔ C := by
  have hNB : (normalizer (P : Set B)).map B.subtype = borel B U := by
    change (sylowNormalizer P).map B.subtype = _
    rw [←borel_subgroupOf_eq_sylowNormalizer B U P hP]
    exact map_subgroupOf_eq_of_le (borel_le B U)
  have hi : (U ⊓ B).relIndex (borel B U) = 3 := by
    rw [←hP,←hNB,relIndex_map_map_of_injective _ _ B.subtype_injective]
    exact a5_sylow_borel_index e P
  have hUC : Disjoint (U ⊓ B) C := by
    have hp : IsPGroup 2 (U ⊓ B : Subgroup G) := hP ▸ P.isPGroup'.map B.subtype
    exact hp.disjoint_of_coprime (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hC))
      (by decide)
  have he := card_sup_eq_mul_of_normalizes_of_disjoint (U ⊓ B) C hCN hUC
  have hle : (U ⊓ B) ⊔ C ≤ borel B U :=
    sup_le (localSylow_le_borel B U) (le_inf hCB hCN)
  have hc := ((U ⊓ B).subgroupOf (borel B U)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (localSylow_le_borel B U)).toEquiv] at hc
  change Nat.card (U ⊓ B : Subgroup G) * (U ⊓ B).relIndex (borel B U) = _ at hc
  rw [hi] at hc
  rw [hC] at he
  exact (eq_of_le_of_card_ge hle (by omega)).symm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

omit [Finite G] in
private theorem cartan_normalizes_commonTwo {X : Subgroup G} :
    X ≤ normalizer (commonTwo T X : Set G) :=
  (le_sup_left : X ≤ X ⊔ (T : Subgroup G)).trans
    ((X ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

private theorem psl_four_a5 {H : Type*} [Group H]
    (h : ClassicalGroup.IsPSL H 2 4) : Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  exact ⟨e.trans a⟩

/-- Identify both original Borels from the original Cartan intersections. -/
theorem original_borels_of_cartan_split (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hm₀ : ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 4)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hsplit : (X ⊓ f.Li 0) ⊔ (X ⊓ f.Li 1) = X ∧
      Disjoint (X ⊓ f.Li 0) (X ⊓ f.Li 1)) :
    ∀ i, borel (locals K₀ (f.Li 1) i) (commonTwo T X) =
      (commonTwo T X ⊓ locals K₀ (f.Li 1) i) ⊔ (X ⊓ locals K₀ (f.Li 1) i) := by
  obtain ⟨hc,h₁,h₀⟩ := first_triangle_cartan_intersections D S f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hc₀ : Nat.card (X ⊓ K₀ : Subgroup G) = 3 := h₀ ▸ hc
  have hc₁ : Nat.card (X ⊓ f.Li 0 : Subgroup G) = 3 := h₁ ▸ hc
  have hc₂ : Nat.card (X ⊓ f.Li 1 : Subgroup G) = 3 := by
    let e := c.cartanTorusEquiv hX
    let : CommGroup X := MonoidHom.commGroupOfInjective e.toMonoidHom e.injective
    have hcomm : X ⊓ f.Li 1 ≤ centralizer (X ⊓ f.Li 0 : Set G) := by
      intro x hx y hy
      exact congrArg Subtype.val (mul_comm (⟨y,hy.1⟩ : X) (⟨x,hx.1⟩ : X))
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint (X ⊓ f.Li 0) (X ⊓ f.Li 1)
      (hcomm.trans (Subgroup.centralizer_le_normalizer _)) hsplit.2
    have h9 : Nat.card X = 9 := by
      rw [c.cartan_card hX,hfour]
      norm_num
    rw [hsplit.1,h9,hc₁] at hh
    omega
  have hn (i : Fin 2) : X ≤ normalizer (locals K₀ (f.Li 1) i : Set G) := by
    fin_cases i
    · exact cartan_normalizes_other_residual D S f hu hm₁ hX hK hLK hK₀ hK₀K hk
    · exact cartan_normalizes_flag_residual D S f hu hX 1
  have hm (i : Fin 2) : Nonempty ((locals K₀ (f.Li 1) i ⧸
      pCore 2 (locals K₀ (f.Li 1) i)) ≃* alternatingGroup (Fin 5)) := by
    apply psl_four_a5
    fin_cases i
    · exact hm₀
    · simpa [hfour,locals] using hm₂
  intro i
  obtain ⟨P,hP⟩ := original_pair_sylow D S f hu hm₁ hX hK hLK hK₀K.le hTK₀ hk i
  apply borel_eq_sylow_sup_cubic P hP (hm i).some inf_le_right
    (inf_le_left.trans ((le_inf cartan_normalizes_commonTwo (hn i)).trans
      inf_normalizer_le_normalizer_inf))
  fin_cases i
  · exact hc₀
  · exact hc₂

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
