module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroNormalizerKernel
public import Theory.GroupTheory.MaximumElementaryPairNormalizer

/-!
# Final normalizer control from the literal zero-center Γ geometry

The source Γ-kernel lies in M, and an escaping Baumann normalizer acts on Γ
as S₄. For the literal Sylow intersection with the preimage of O₂(S₄),
Frattini gives generation by the kernel and its normalizer. The four-factor
geometry says that this intersection normalizes only two maximum elementary
subgroups of S, one being the original module V. Since T fixes V, the
maximum-pair/Sylow argument fixes V throughout the remaining normalizer.
Consequently the whole Baumann normalizer lies in M, a contradiction.

The geometric marking and its two-candidate conclusion are explicit inputs
being supplied by the independent four-factor construction. No desired
normalizer containment or final automorphism assertion is an input.
Source: Aschbacher–Smith 10.2.1, first paragraph of printed p.743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_a5_zero_normalizer_contradiction_of_gamma_geometry
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (F : Fin 4 → Subgroup G) (E : Fin 4 → Type*) [∀ i, Group (E i)]
    [∀ i, Finite (E i)] [∀ i, IsElementaryAbelian 2 (E i)]
    (eF : ∀ i, F i ≃* DihedralGroup 4 × E i)
    (hTF : ∀ t ∈ (T : Subgroup G), ∀ i,
      ∃ j, (F i).map (MulAut.conj t).toMonoidHom = F j)
    (hcard : ∀ i, Nat.card (D.moduleSubgroup ⊓ F i : Subgroup G) = 4 * Nat.card (E i))
    (hspan : (⨆ i, D.moduleSubgroup ⊓ F i) = D.moduleSubgroup)
    (f : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) →* Equiv.Perm (Fin 4))
    (hf : ∀ (n : normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) i,
      (F i).map (MulAut.conj (n : G)).toMonoidHom = F (f n i))
    (himage : Nat.card (((T : Subgroup G).subgroupOf
      (normalizer (ChapterB.baumann (T : Subgroup G) : Set G))).map f) = 8)
    (hV : D.moduleSubgroup ∈ elementaryAbelianMaxSubgroups (ChapterB.baumann (T : Subgroup G)))
    (A : Subgroup G)
    (hpair : let N := normalizer (ChapterB.baumann (T : Subgroup G) : Set G)
      let R := (((T : Subgroup G).subgroupOf N) ⊓
        (pCore 2 (Equiv.Perm (Fin 4))).comap f).map N.subtype
      ∀ W ∈ elementaryAbelianMaxSubgroups (ChapterB.baumann (T : Subgroup G)),
        R ≤ normalizer (W : Set G) → W = D.moduleSubgroup ∨ W = A) : False := by
  let S := ChapterB.baumann (T : Subgroup G)
  let N := normalizer (S : Set G)
  let U := (pCore 2 (Equiv.Perm (Fin 4))).comap f
  let Rn := ((T : Subgroup G).subgroupOf N) ⊓ U
  let R := Rn.map N.subtype
  have hTN : (T : Subgroup G) ≤ N := (T : Subgroup G).le_normalizer.trans
    (normalizer_le_normalizer_baumann (T : Subgroup G))
  let P := T.subtype hTN
  have hR : R = (T : Subgroup G) ⊓ U.map N.subtype := by
    change (((T : Subgroup G).subgroupOf N) ⊓ U).map N.subtype = _
    rw [map_inf _ _ _ N.subtype_injective,map_subgroupOf_eq_of_le hTN]
  have hNU : N ≤ normalizer (U.map N.subtype : Set G) := by
    have hh := U.le_normalizer_map N.subtype
    rw [show normalizer (U : Set N) = ⊤ from U.normalizer_eq_top,
      ← MonoidHom.range_eq_map,N.range_subtype] at hh
    exact hh
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    rw [hR]
    exact (le_inf (T : Subgroup G).le_normalizer (hTN.trans hNU)).trans
      inf_normalizer_le_normalizer_inf
  have hRT : R ≤ (T : Subgroup G) := hR.le.trans inf_le_left
  have hVnorm := source_a5_zero_centralizer_module_normalizer D e hn hout hz
  have hcontrol : normalizer (S : Set G) ⊓ normalizer (R : Set G) ≤ D.maximalLocal :=
    (paired_maximum_elementary_normalizer_control T S R D.moduleSubgroup A hTN hTR
      D.sylow_normalizes_module hV (hRT.trans D.sylow_normalizes_module) hpair).trans hVnorm.le
  have hsurj := source_a5_zero_normalizer_action_surjective D e hn hout hz
    F E eF hTF hcard hspan f hf himage
  have hgen := normalizer_sylow_core_preimage_sup_kernel_eq_top P f hsurj
    (pCore 2 (Equiv.Perm (Fin 4))) pCore_isPGroup
  have hgenG := congrArg (Subgroup.map N.subtype) hgen
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,N.range_subtype] at hgenG
  have hKN := source_a5_zero_normalizer_kernel_le D e hn hout hz F E eF hTF hcard hspan
  apply hout
  change N ≤ D.maximalLocal
  rw [←hgenG]
  apply sup_le
  · apply le_trans (le_inf (map_le_range N.subtype _ ) (Rn.le_normalizer_map N.subtype))
    simpa only [N.range_subtype] using hcontrol
  · rintro _ ⟨n,hn,rfl⟩
    apply hKN
    apply mem_iInf.mpr
    intro i
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (F i).map (MulAut.conj (n : G)).toMonoidHom = F i
    exact (hf n i).trans (by rw [show f n = 1 from hn]; rfl)

end CFSG.Quasithin.Chapter10
