module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullCoordinates
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Perpendicular
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import Theory.Representation.BinaryPermutation.EightPointInterval
public import Theory.GroupTheory.SylowNormalizedResidual

/-!
# Irreducibility on the original point quotient

Intersect the original Sylow with L inside LT and map that Sylow through
L/C_L(V) to A₈. The marked nonidentity point is fixed by this image, hence
is singular for the half-weight form. Every even permutation fixing the
point lifts to C_L(z); the residual--Sylow supplement puts this centralizer
inside the literal L₁T. Transporting an invariant subgroup through the full
coordinates now gives an invariant interval in the permutation six-space,
so it equals V₁ or V₅.

This proves 12.6.24(1) from the original source data, with the earlier
C_V(L)=1 and T-invariance of V₁ explicit. There is no irreducibility,
point-coordinate, or second-action premise. The original module, quotient
projection and conjugation-kernel quotient remain unchanged.
Source: Aschbacher--Smith, 12.6.23--24, printed pp.830--831.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section06
open BinaryPermutation
variable {G : Type*} [Group G] [Finite G]
  {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis K T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original Sylow-fixed point is singular; its image Sylow is taken
through the literal L-action kernel quotient. -/
theorem SourceHypothesis.original_point_singular
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    ¬ D.Nonsingular z := by
  let E := D.fullSetup hZ T z
  let J := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal A
  let e : A ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let f : A →* alternatingGroup (Fin 8) := D.groupEquiv.toMonoidHom.comp
    ((QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker).comp e.toMonoidHom)
  have hf : Function.Surjective f := D.groupEquiv.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e.surjective)
  let Q := P.mapSurjective (f := f) hf
  have hTC : (T : Subgroup G) ≤ E.Gz := hTz.trans
    (normalizer_le_centralizer_of_card_two E.V₁ (E.point_card hz))
  have hfix : ∀ g ∈ (Q : Subgroup (alternatingGroup (Fin 8))),
      naturalRepresentation (Fin 8) g.val (D.fullCoordinates hZ z).toAdd=
        (D.fullCoordinates hZ z).toAdd := by
    rintro g ⟨a,ha,rfl⟩
    have hat : (e a : G) ∈ (T : Subgroup G) := by
      rw [hP] at ha
      exact ha
    have he : conjugation L V S.chosen.normalizes (e a) z=z := by
      apply Subtype.ext
      have hh := hTC hat z.val (mem_zpowers _)
      change (e a : G)*z.val*(e a : G)⁻¹=z.val
      rw [←hh,mul_inv_cancel_right]
    exact (D.fullCoordinates_equivariant hZ (e a) z).symm.trans
      (congrArg (fun v : V => (D.fullCoordinates hZ v).toAdd) he)
  have hs := EightPointInterval.sylow_fixed_singular Q (D.fullCoordinates hZ z).toAdd hfix
  intro hn
  exact ((D.fullCoordinates_nonsingular_iff hZ z).mpr hn) hs

/-- The original point quotient is irreducible for L₁T. Singularity of
the chosen Sylow-fixed point is proved above; only vanishing of C_V(L)
remains an earlier-source input. -/
theorem SourceHypothesis.original_point_quotient_irreducible
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (W : Subgroup G) (hpoint : (D.fullSetup hZ T z).V₁ ≤ W)
    (hperp : W ≤ (D.fullSetup hZ T z).V₅)
    (hinv : (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤ normalizer (W : Set G)) :
    W=(D.fullSetup hZ T z).V₁ ∨ W=(D.fullSetup hZ T z).V₅ := by
  let E := D.fullSetup hZ T z
  let e := D.fullCoordinates hZ
  let U : Submodule (ZMod 2) (natural (Fin 8)) :=
    AddSubgroup.toZModSubmodule 2 ((W.subgroupOf V).map e.toMonoidHom).toAddSubgroup'
  have hmem (v : V) : (e v).toAdd ∈ U ↔ v.val ∈ W := by
    constructor
    · rintro ⟨w,hw,he⟩
      exact e.injective he ▸ hw
    · intro hv
      exact ⟨v,hv,rfl⟩
  have hTG : (T : Subgroup G) ≤ normalizer (E.Gz : Set G) :=
    hTz.trans (normalizer_le_normalizer_centralizer _)
  have hTLG : (T : Subgroup G) ≤ normalizer (L ⊓ E.Gz : Set G) :=
    (le_inf S.chosen.sylow_normalizes_component hTG).trans inf_normalizer_le_normalizer_inf
  have hCL : L ⊓ E.Gz ≤ E.L₁ ⊔ (T : Subgroup G) :=
    le_embedded_pResidual_sup_sylow_of_normalizes T (L ⊓ E.Gz) hTLG
  have he0 : (e z).toAdd ≠ 0 := by
    intro he
    exact hz (e.injective (he.trans e.map_one.symm))
  have hes : TerminalOrthogonal.Eight.form (e z).toAdd=0 := by
    by_contra hn
    exact S.original_point_singular D hZ z hz hTz ((D.fullCoordinates_nonsingular_iff hZ z).mp hn)
  have hup : ∀ w ∈ U, TerminalOrthogonal.Eight.form.polarBilin (e z).toAdd w=0 := by
    rintro _ ⟨v,hv,rfl⟩
    exact (E.mem_V₅_iff v).mp (hperp hv)
  have hi : ∀ g : alternatingGroup (Fin 8), naturalRepresentation (Fin 8) g.val (e z).toAdd=(e z).toAdd →
      ∀ w ∈ U, naturalRepresentation (Fin 8) g.val w ∈ U := by
    intro g hg
    obtain ⟨l,hl⟩ := (D.groupEquiv.surjective.comp
      (QuotientGroup.mk'_surjective (conjugation L V S.chosen.normalizes).ker)) g
    change D.groupEquiv (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker l)=g at hl
    have heq (v : V) := D.fullCoordinates_equivariant hZ l v
    simp only [hl] at heq
    have hlz : conjugation L V S.chosen.normalizes l z=z :=
      e.injective ((heq z).trans hg)
    have hcg : l.val ∈ E.Gz := by
      rw [E.Gz_eq,mem_centralizer_singleton_iff]
      have hh := congrArg Subtype.val hlz
      change l.val*z.val*l.val⁻¹=z.val at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hn := hinv (hCL ⟨l.property,hcg⟩)
    rintro _ ⟨v,hv,rfl⟩
    change naturalRepresentation (Fin 8) g.val (D.fullCoordinates hZ v).toAdd ∈ U
    rw [←heq v]
    apply (hmem _).mpr
    exact (Subgroup.mem_normalizer_iff.mp hn v.val).mp hv
  rcases EightPointInterval.singular_invariant_interval (e z).toAdd he0 hes U
      ((hmem z).mpr (hpoint (mem_zpowers _))) hup hi with hsmall | hfull
  · left
    apply le_antisymm _ hpoint
    intro w hw
    let v : V := ⟨w,E.V₅_le (hperp hw)⟩
    rcases hsmall (e v).toAdd ((hmem v).mpr hw) with he | he
    · have hv : v=1 := e.injective (he.trans e.map_one.symm)
      have hval := congrArg Subtype.val hv
      change w=1 at hval
      rw [hval]
      exact one_mem _
    · have hv : v=z := e.injective he
      have hval := congrArg Subtype.val hv
      change w=z.val at hval
      rw [hval]
      exact mem_zpowers _
  · right
    apply le_antisymm hperp
    intro w hw
    let v : V := ⟨w,E.V₅_le hw⟩
    exact (hmem v).mp (hfull (e v).toAdd ((E.mem_V₅_iff v).mp hw))
end CFSG.Quasithin.Chapter12.Section06
