module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Cubic
public import Theory.GroupTheory.PGroup.ExtraspecialThreeCubicLifts
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.Quasithin.TwoKernelSubgroupRank

/-!
# Lifting the source cubics through the full quotient kernel

A cubic in the marked local quotient is lifted by taking the two-residual
of its full preimage. This subgroup maps onto that cubic even when the
extension does not split. Its join with the original Sylow has the same
quotient by the two-core as the corresponding quotient join. Thus the
literal S₃ hypothesis of 14.7.2 applies, and fixation in a proper module
quotient gives a lift in the original plane centralizer.

Two such source cubics therefore contribute their full three-rank to that
centralizer. The hypothesis on each Sylow join is essential; no assertion
about arbitrary cubic stabilizers is made.

Source: Aschbacher–Smith 14.7.2(3), p.1043, as used in the last paragraph
of 14.7.50, p.1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u v w w'
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual source cubic lifts into the original plane centralizer, with
its entire two-kernel retained. The S₃ condition concerns its Sylow join. -/
theorem local_cubic_le_plane_centralizer_image_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    {D : Type v} [Group D] [Finite D]
    (π : I →* D) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    {W : Type w} {X : Type w'} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) I W} {τ : Representation (ZMod 2) D X}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap (τ.comp π)) (hp : p.toLinearMap.ker ≠ ⊤)
    (B : Subgroup D) (hB : Nat.card B = 3)
    (he : Nonempty (((B ⊔ ((T : Subgroup G).subgroupOf I).map π : Subgroup D) ⧸
      pCore 2 (B ⊔ ((T : Subgroup G).subgroupOf I).map π : Subgroup D)) ≃*
        Equiv.Perm (Fin 3)))
    (hfix : ∀ b ∈ B, ∀ z : F.UH I, (z : G) ∈ F.Vi 2 →
      τ b (p (c.coordinates z).toAdd) = p (c.coordinates z).toAdd) :
    B ≤ ((centralizer (F.Vi 2 : Set G)).subgroupOf I).map π := by
  obtain ⟨A,_hAR,hAp,_hSA,_hkA,hAB,_hAk,_hAc⟩ :=
    exists_cubic_residual_lift π hπ hk (⊥ : Subgroup I) B hB (by simp)
  let Y := A.map I.subtype
  have hYI : Y ≤ I := map_subtype_le A
  have hYp : IsPPerfect 2 Y := hAp.of_surjective
    (I.subtype.subgroupMap A) (I.subtype.subgroupMap_surjective A)
  let J := Y ⊔ (T : Subgroup G)
  have hJI : J ≤ I := sup_le hYI (F.sylow_le_of_mem_Hz hI)
  let f := π.comp (inclusion hJI)
  let P := B ⊔ ((T : Subgroup G).subgroupOf I).map π
  have hAJ : J.subgroupOf I = A ⊔ (T : Subgroup G).subgroupOf I := by
    rw [subgroupOf_sup hYI (F.sylow_le_of_mem_Hz hI)]
    congr 1
    exact comap_map_eq_self_of_injective I.subtype_injective A
  have him : f.range = P := by
    rw [MonoidHom.range_comp,inclusion_range,hAJ,Subgroup.map_sup,hAB]
  have hfk : IsPGroup 2 f.ker := hk.comap_of_injective
    (inclusion hJI) (inclusion_injective hJI)
  have hfrk : IsPGroup 2 f.rangeRestrict.ker := by
    have hh : f.rangeRestrict.ker = f.ker := by
      ext x
      exact Subtype.ext_iff
    rwa [hh]
  let ef := f.rangeRestrict.pCoreQuotientEquiv f.rangeRestrict_surjective hfrk
  let er := MulEquiv.subgroupCongr him
  let eq := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  obtain ⟨e⟩ := he
  have heY : Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) :=
    ⟨ef.trans (eq.trans e)⟩
  have hcentral : ⁅F.Vi 2,Y⁆ = ⊥ := local_quotient_plane_fixed_at
    h hab structural previous faithful I hI c p hp Y hYI hYp heY (by
      intro y hy z hz
      obtain ⟨a,ha,hay⟩ := hy
      have ha' : (⟨y,hYI ⟨a,ha,hay⟩⟩ : I) = a := Subtype.ext hay.symm
      change τ (π ⟨y,_⟩) (p (c.coordinates z).toAdd) = p (c.coordinates z).toAdd
      rw [ha']
      exact hfix (π a) (hAB ▸ mem_map_of_mem π ha) z hz)
  have hYC : Y ≤ centralizer (F.Vi 2 : Set G) := by
    rw [commutator_comm] at hcentral
    exact commutator_eq_bot_iff_le_centralizer.mp hcentral
  rw [←hAB]
  apply map_mono
  intro a ha
  exact hYC (mem_map_of_mem I.subtype ha)

/-- Source cubics satisfying the literal S₃-over-Sylow condition retain
their joint three-rank in the original plane centralizer. -/
theorem local_two_cubic_plane_centralizer_rank_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    {D : Type v} [Group D] [Finite D]
    (π : I →* D) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    {W : Type w} {X : Type w'} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) I W} {τ : Representation (ZMod 2) D X}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap (τ.comp π)) (hp : p.toLinearMap.ker ≠ ⊤)
    (B E : Subgroup D)
    (hrows : ∀ A ∈ ({B,E} : Set (Subgroup D)), Nat.card A = 3 ∧
      Nonempty (((A ⊔ ((T : Subgroup G).subgroupOf I).map π : Subgroup D) ⧸
        pCore 2 (A ⊔ ((T : Subgroup G).subgroupOf I).map π : Subgroup D)) ≃*
          Equiv.Perm (Fin 3)) ∧
      ∀ a ∈ A, ∀ z : F.UH I, (z : G) ∈ F.Vi 2 →
        τ a (p (c.coordinates z).toAdd) = p (c.coordinates z).toAdd) :
    primeRank 3 (B ⊔ E : Subgroup D) ≤ primeRank 3 (centralizer (F.Vi 2 : Set G)) := by
  let C := (centralizer (F.Vi 2 : Set G)).subgroupOf I
  have hlift (A : Subgroup D) (hA : A ∈ ({B,E} : Set (Subgroup D))) : A ≤ C.map π := by
    obtain ⟨hcard,he,hfix⟩ := hrows A hA
    exact local_cubic_le_plane_centralizer_image_at h hab structural previous faithful
      I hI π hπ hk c p hp A hcard he hfix
  have hjoin : B ⊔ E ≤ C.map π := sup_le (hlift B (by simp)) (hlift E (by simp))
  let f := π.subgroupMap C
  have hfk : IsPGroup 2 f.ker := by
    have he : f.ker = π.ker.comap C.subtype := by
      ext x
      exact Subtype.ext_iff
    rw [he]
    exact hk.comap_subtype
  have hr : primeRank 3 C = primeRank 3 (C.map π) := by
    apply primeRank_eq_of_surjective_of_coprime 3 f (π.subgroupMap_surjective C)
    obtain ⟨n,hn⟩ := hfk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hc : primeRank 3 C ≤ primeRank 3 (centralizer (F.Vi 2 : Set G)) := by
    let f : C →* centralizer (F.Vi 2 : Set G) :=
      (I.subtype.comp C.subtype).codRestrict _ (fun x => x.property)
    exact Theory.GroupTheory.primeRank_le_of_injective 3 f
      (fun x y he => Subtype.ext (Subtype.ext
        (congrArg (fun z : centralizer (F.Vi 2 : Set G) => (z : G)) he)))
  exact (primeRank_mono 3 hjoin).trans (hr ▸ hc)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
