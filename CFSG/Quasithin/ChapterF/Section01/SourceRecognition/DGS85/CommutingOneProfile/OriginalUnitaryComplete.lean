module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryCoreProfile

/-!
# Original marked unitary central layers and natural quotient

The original PSU3 or SU3 marking supplies an escaping four-walk and its
transitivity. Applying the earlier local results to that actual walk proves
that the full alpha second kernel and beta third kernel vanish, and that the
beta second-kernel radical is the source center. Its order is taken from the
same marked degree, including degree one.

The same construction and the proved nonelementarity of the full-Borel
quotient identify the beta-core center, derived subgroup and Frattini subgroup,
and the center of the full Borel two-core. All are the literal original image
of Z_beta. The core has order 2^(7m), class two and exponent dividing four.
The constructed natural coordinate surjection descends to an actual
isomorphism on the literal alpha quotient, preserving conjugation by the
original local actor. No initial path, natural-action or central-layer
premise is used.

These are the unitary marked central-layer consequences, not the complete
Chapter 11 classification. Catalogue selection, the elementary and mixed
branches, and final marked amalgam recognition remain separate obligations.
Source: DGS85, Groups and Graphs (1985), (11.3)(e), (11.6), (11.8)(e,f),
pp.169--176; the full-kernel consequences are in AlphaSecondKernel.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial NoncommutingProfile Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

variable (h : HypothesisF11 L₀ S₀)
    (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false) (base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false),Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false)).map ((Reduction.G₀ L₀ S₀)).subtype)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype)) 3 (2^m) ∨
      IsSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype)) 3 (2^m))

include h hc hb hcomm Ma hm mark

/-- Full kernel depths and the exact beta second-kernel radical, with all
path premises constructed and the original marked degree preserved. -/
theorem original_borel_unitary_second_kernel_profile_from_marking :
    (ballKernel F₀ (base F₀ false) 2).map (G₀).subtype = ⊥ ∧
      (ballKernel F₀ (base F₀ true) 3).map (G₀).subtype = ⊥ ∧
      ((ballKernel F₀ (base F₀ true) 2).map (G₀).subtype).pCoreIn 2 =
        (Z F₀ (base F₀ true)).map (G₀).subtype ∧
      Nat.card (((ballKernel F₀ (base F₀ true) 2).map (G₀).subtype).pCoreIn 2) = 2^m ∧
      (ballKernel F₀ (base F₀ true) 2).map (G₀).subtype ≠ ⊥ := by
  let d := reducedFullEarlierLocalTheorems h
  have Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) :=
    mark.elim (IsRankOneModel.projective_unitary m hm) (IsRankOneModel.special_unitary m hm)
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ :=
    original_unitary_escaping_four_walk h hc hb hcomm Ma hm mark
  have ht := original_unitary_four_walk_transitive_from_marking h hc hb hcomm Ma hm mark (g • c)
  obtain ⟨hα,hβ,hR,hRne⟩ := original_reduced_second_kernels_on_escaping_path h d
    hc hb hcomm hbc hac Ma Mb g hga hgb hesc (r := 3) ht p hp
    (by rw [hpv]; simp) (by rw [hpv]; simp) (by rw [hpv]; simp)
    (by rw [hpv]; simp) (by rw [hpv]; simp)
  refine ⟨hα,hβ,hR,?_,hRne⟩
  rw [hR]
  exact (original_unitary_centers_and_field h hc hb hcomm Ma hm mark).2.1

/-- The special beta core and the full Borel have the same source center.
The field degree in every order is the supplied original PSU/SU degree. -/
theorem original_borel_unitary_beta_layers_from_marking :
    let R := (Q F₀ (base F₀ true)).map (G₀).subtype
    let C := (Z F₀ (base F₀ true)).map (G₀).subtype
    Nat.card R = 2^(7*m) ∧ Nat.card C = 2^m ∧
      centerIn R = C ∧ ⁅R,R⁆ = C ∧ (frattini R).map R.subtype = C ∧
      centerIn (twoCore (commonBorel L₀ S₀)) = C ∧
      (∀ x ∈ R, x^4 = 1) ∧ ⁅⁅R,R⁆,R⁆ = ⊥ ∧ ⁅R,R⁆ ≠ ⊥ ∧
      ∃ hN : (C.subgroupOf R).Normal, letI := hN
        IsElementaryAbelian 2 (R ⧸ C.subgroupOf R) := by
  let d := reducedFullEarlierLocalTheorems h
  have Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) :=
    mark.elim (IsRankOneModel.projective_unitary m hm) (IsRankOneModel.special_unitary m hm)
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ :=
    original_unitary_escaping_four_walk h hc hb hcomm Ma hm mark
  have ht := original_unitary_four_walk_transitive_from_marking h hc hb hcomm Ma hm mark (g • c)
  have hne := original_borel_unitary_quotient_not_elementary h hm mark
  obtain ⟨_,_,_,_,_,_,hcent,hder,hphi,hedge,hpow,hcl,hnon,hN,helem⟩ :=
    original_borel_unitary_beta_profile_on_escaping_path h d hc hb hcomm hbc hac
      Ma Mb g hga hgb hesc (r := 3) ht p hp
      (by rw [hpv]; simp) (by rw [hpv]; simp) (by rw [hpv]; simp)
      (by rw [hpv]; simp) (by rw [hpv]; simp) hne
  exact ⟨(original_borel_unitary_core_orders_from_marking h hc hb hcomm Ma hm mark).1,
    (original_unitary_centers_and_field h hc hb hcomm Ma hm mark).2.1,
    hcent,hder,hphi,hedge,hpow,hcl,hnon,hN,helem⟩

/-- Equivariant natural coordinates on the literal original alpha quotient.
Both the denominator and the local actor use the original inclusion maps. -/
theorem original_borel_unitary_alpha_natural_quotient_from_marking :
    let R := (Q F₀ (base F₀ false)).map (G₀).subtype
    let C := (Z F₀ (base F₀ false)).map (G₀).subtype
    let L := (graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype
    (frattini R).map R.subtype = C ∧
      ∃ hN : (C.subgroupOf R).Normal, letI := hN
        ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
          Nat.card k = 2^(2*m) ∧
          ∃ ea : (L ⧸ pCore 2 L) ≃* SL(2,k),
            ∃ e : (R ⧸ C.subgroupOf R) ≃* Multiplicative (Fin 2 → k),
              ∀ (l : L) (x y : R), (y : G) = (l : G) * (x : G) * (l : G)⁻¹ →
                (e (QuotientGroup.mk' (C.subgroupOf R) y)).toAdd =
                  Matrix.mulVec (ea (QuotientGroup.mk' (pCore 2 L) l)).val
                    (e (QuotientGroup.mk' (C.subgroupOf R) x)).toAdd := by
  let R := (Q F₀ (base F₀ false)).map (G₀).subtype
  let C := (Z F₀ (base F₀ false)).map (G₀).subtype
  obtain ⟨hphi,k,hfield,hfinite,hchar,hcard,ea,f,hf,hker,hact⟩ :=
    original_borel_unitary_alpha_natural_from_marking h hc hb hcomm Ma hm mark
  let hN : (C.subgroupOf R).Normal := by rw [←hker]; infer_instance
  let e : (R ⧸ C.subgroupOf R) ≃* Multiplicative (Fin 2 → k) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he (x : R) : e (QuotientGroup.mk' (C.subgroupOf R) x) = f x := rfl
  refine ⟨hphi,hN,k,hfield,hfinite,hchar,hcard,ea,e,?_⟩
  intro l x y hy
  rw [he,he]
  exact hact l x y hy

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
