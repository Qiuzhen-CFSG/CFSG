module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.PlacedEndpoint
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ConjugateSection
public import Theory.Representation.BinaryOffender.LineDisplacementObstruction
public import Theory.Representation.BinaryOffender.QuadraticConstituentStability

/-!
# Small movement at the opposite terminal endpoint

The common commutator line bounds the displacement of each individual actor
by one plus the rank of the literal opposite-core denominator. Transporting
the original section along the critical conjugator gives this bound on
U^g/Z^g without selecting a new endpoint or assuming equal endpoint ranks.

A placed actor has rank at most two. An element of U therefore moves at most
three dimensions on U^g/Z^g, whereas interchanging the two disjoint component
supports moves at least six. Thus U normalizes both literal conjugate
components. This is the swapping exclusion in the diagonal-alignment step
of Aschbacher--Smith 14.6.24(3), printed p.1040.

The actual support markings remain earlier inputs, owned by
qt-e-suitable-component-marking under the 14.6.20--23 support conclusions.
The final suitable-choice assembly remains with qt-e-suitable-existence.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- Each individual actor moves at most one plus the rank of the literal
commutator denominator. No quadratic-member comparison is required. -/
theorem section_cyclic_movement_le
    {H U Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) E}
    (s : ConjugationSection H U Z ρ) (A C : Subgroup G)
    (hAH : A ≤ H) (hUC : U ≤ normalizer (C : Set G))
    (hAC : A ≤ normalizer (C : Set G)) (hC : Nat.card C = 2)
    (a : Source.Hstar H) (ha : a ∈ Source.starImage H A) :
    fixedCodim ρ (zpowers a) ≤
      1 + Nat.log 2 ((commutatorPreimage U A C).relIndex U) := by
  let B := Source.starImage H A
  let D := commutatorPreimage U A C
  have hn : A ≤ normalizer (D : Set G) :=
    commutatorPreimage_normalized U A C A hUC (hAH.trans s.normalizes)
      A.le_normalizer hAC
  let τ := ρ.comp B.subtype
  let W : Subrepresentation τ := {
    toSubmodule := s.image D
    apply_mem_toSubmodule := by
      rintro ⟨b,hb⟩ v hv
      obtain ⟨x,hx,rfl⟩ := hb
      obtain ⟨u,hu,rfl⟩ := (s.mem_image D v).mp hv
      change ρ (QuotientGroup.mk' (pCore 2 H) x) (s.quotient u).toAdd ∈ s.image D
      rw [s.conjugates]
      exact ⟨_,(mem_normalizer_iff.mp (hn hx) u).mp hu,rfl⟩ }
  obtain ⟨hdim,hdisp⟩ := s.critical_line_displacement A C hUC hC
  have hb := fixedCodim_zpowers_le_codim_add_center τ W (⟨a,ha⟩ : B)
    (s.image C) (fun v => hdisp a ha v v.property)
  have he := fixedCodim_map_equivariant τ ρ B.subtype (LinearEquiv.refl _ _)
    (fun _ _ => rfl) (zpowers (⟨a,ha⟩ : B))
  rw [MonoidHom.map_zpowers] at he
  have hd : Module.finrank (ZMod 2) (E ⧸ W.toSubmodule) =
      Nat.log 2 (D.relIndex U) := s.quotient_finrank D (s.line_le_DH A C hAH)
  calc
    fixedCodim ρ (zpowers a) = fixedCodim τ (zpowers (⟨a,ha⟩ : B)) := he.symm
    _ ≤ _ := hb
    _ ≤ _ := Nat.add_le_add hdim hd.le

/-- The same original endpoint bounds each element of U on U^g/Z^g by
one plus the original star-actor rank. -/
theorem endpoint_opposite_cyclic_movement_le
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b)
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (a : Source.Hstar (i.conjugate D.H))
    (ha : a ∈ Source.starImage (i.conjugate D.H) D.UH) :
    fixedCodim (ρ.comp (starEquiv (MulAut.conj i.representative) D.H).symm.toMonoidHom)
      (zpowers a) ≤ 1 + rank (Source.starImage D.H (i.conjugate D.UH)) := by
  let s := conjugateSection (criticalSection h c) (MulAut.conj i.representative)
  have huv : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hUH : D.UH ≤ i.conjugate D.H := huv.trans (i.reverse_le hb)
  have hUgH : i.conjugate D.UH ≤ D.H := (map_mono huv).trans (i.large_le hb)
  have hm := section_cyclic_movement_le s D.UH D.V₁ hUH
    (hUgH.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
    (h.UH_le_H.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
    h.point_card a ha
  rw [(i.denominators h hb).2] at hm
  change _ ≤ 1 + Nat.log 2 (Nat.card (((i.conjugate D.UH).subgroupOf D.H).map
    (QuotientGroup.mk' (pCore 2 D.H))))
  rw [i.actor_card h hb]
  exact hm

/-- A rank-at-most-two critical actor forces the opposite module to preserve
both large component supports, without a rank comparison at the other end. -/
theorem endpoint_opposite_preserves_pair
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b)
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (hr : rank (Source.starImage D.H (i.conjugate D.UH)) ≤ 2)
    (I J : Submodule (ZMod 2) E) (hd : Disjoint I J)
    (hdim : 3 < Module.finrank (ZMod 2) I)
    (hperm : ∀ a : Source.Hstar D.H,
      (I.map (ρ a) = I ∧ J.map (ρ a) = J) ∨
      (I.map (ρ a) = J ∧ J.map (ρ a) = I)) :
    let τ := ρ.comp (starEquiv (MulAut.conj i.representative) D.H).symm.toMonoidHom
    ∀ a ∈ Source.starImage (i.conjugate D.H) D.UH,
      I.map (τ a) = I ∧ J.map (τ a) = J := by
  intro τ a ha
  rcases hperm ((starEquiv (MulAut.conj i.representative) D.H).symm a) with hs | hs
  · exact hs
  · have hm := endpoint_opposite_cyclic_movement_le h i hb c a ha
    have hl := finrank_le_fixedCodim_of_disjoint_map τ I (mem_zpowers a)
      (by change Disjoint I (I.map (ρ ((starEquiv (MulAut.conj i.representative) D.H).symm a))); rw [hs.1]; exact hd)
    change fixedCodim τ (zpowers a) ≤ _ at hm
    omega

/-- Translate support stabilization on the transported quotient back to
normalization of the literal conjugate component subgroups. -/
theorem endpoint_opposite_normalizes_components
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b)
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (hr : rank (Source.starImage D.H (i.conjugate D.UH)) ≤ 2)
    (I J : Submodule (ZMod 2) E) (hd : Disjoint I J)
    (hdim : 3 < Module.finrank (ZMod 2) I)
    (hperm : ∀ a : Source.Hstar D.H,
      (I.map (ρ a) = I ∧ J.map (ρ a) = J) ∨
      (I.map (ρ a) = J ∧ J.map (ρ a) = I))
    (K Kplus : Subgroup G)
    (hK : (normalizer (K : Set G)).subgroupOf D.H =
      (subspaceStabilizer ρ I).comap (QuotientGroup.mk' (pCore 2 D.H)))
    (hKplus : (normalizer (Kplus : Set G)).subgroupOf D.H =
      (subspaceStabilizer ρ J).comap (QuotientGroup.mk' (pCore 2 D.H))) :
    D.UH ≤ normalizer (i.conjugate K : Set G) ∧
      D.UH ≤ normalizer (i.conjugate Kplus : Set G) := by
  let e := MulAut.conj i.representative
  let f := D.H.equivMapOfInjective e.toMonoidHom e.injective
  have hUH : D.UH ≤ i.conjugate D.H :=
    (conjugateSpanBy_mono h.plus_le le_rfl).trans (i.reverse_le hb)
  have hs := endpoint_opposite_preserves_pair h i hb c hr I J hd hdim hperm
  have hn (L : Subgroup G) (S : Submodule (ZMod 2) E)
      (hL : (normalizer (L : Set G)).subgroupOf D.H =
        (subspaceStabilizer ρ S).comap (QuotientGroup.mk' (pCore 2 D.H)))
      (hS : ∀ a ∈ Source.starImage (i.conjugate D.H) D.UH,
        S.map ((ρ.comp (starEquiv e D.H).symm.toMonoidHom) a) = S) :
      D.UH ≤ normalizer (i.conjugate L : Set G) := by
    intro u hu
    let x : i.conjugate D.H := ⟨u,hUH hu⟩
    have hx := hS (QuotientGroup.mk' (pCore 2 (i.conjugate D.H)) x)
      (mem_map_of_mem (QuotientGroup.mk' (pCore 2 (i.conjugate D.H))) hu)
    change S.map (ρ ((starEquiv e D.H).symm
      (QuotientGroup.mk' (pCore 2 (i.conjugate D.H)) x))) = S at hx
    rw [starEquiv_symm_mk] at hx
    have hy : f.symm x ∈ (normalizer (L : Set G)).subgroupOf D.H := by
      rw [hL]
      exact (subspace_map_eq_iff ρ S _).mp hx
    have he : e (f.symm x : G) = u := congrArg Subtype.val (f.apply_symm_apply x)
    change u ∈ normalizer (L.map e.toMonoidHom : Set G)
    rw [←map_equiv_normalizer_eq]
    exact ⟨f.symm x,hy,he⟩
  exact ⟨hn K I hK (fun a ha => (hs a ha).1),
    hn Kplus J hKplus (fun a ha => (hs a ha).2)⟩

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The original placed endpoint has normalization in both directions.
This rules out the swapping alternative in the diagonal alignment argument
on p.1040, retaining H=Mc and the original endpoint representative. -/
theorem source_placedEndpoint_opposite_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (K Kplus : Subgroup G)
    (p : PlacedEndpoint
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) K Kplus)
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (c : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) (ρ.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (I J : Submodule (ZMod 2) E) (hd : Disjoint I J)
    (hdim : Module.finrank (ZMod 2) I = 6)
    (hperm : ∀ a : Source.Hstar Mc,
      (I.map (ρ a) = I ∧ J.map (ρ a) = J) ∨
      (I.map (ρ a) = J ∧ J.map (ρ a) = I))
    (hK : (normalizer (K : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ I).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (hKplus : (normalizer (Kplus : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ J).comap (QuotientGroup.mk' (pCore 2 Mc))) :
    conjugateSpanBy (localModule T M) Mc ≤ normalizer (p.endpoint.conjugate K : Set G) ∧
      conjugateSpanBy (localModule T M) Mc ≤ normalizer (p.endpoint.conjugate Kplus : Set G) := by
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab
    Mc (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  exact endpoint_opposite_normalizes_components _ p.endpoint hb c p.rank_le_two
    I J hd (by omega) hperm K Kplus hK hKplus

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
