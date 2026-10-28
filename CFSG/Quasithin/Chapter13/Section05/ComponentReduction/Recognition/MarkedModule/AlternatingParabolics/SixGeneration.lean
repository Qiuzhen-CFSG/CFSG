module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.SixParabolic
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.LinearGeneration
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.Basic
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.SixGeneration.CoreCover

/-!
# Whole-module generation in the S₆ branch of 13.5.21

The selected component maps to the actual alternating subgroup under the
supplied S₆ equivalence: normality gives containment of A₆, while perfectness
kills the sign. Restriction of the original Sylow to this component and the
projection of the original seed supply the marked plane calculation.

The earlier seed identity gives full K*-generation, so the literal projection
by K*-fixed vectors is a perfect central cover of the natural module. The
augmentation-core calculation proves full L₁*-generation on this cover,
including its central kernel. LinearGeneration then carries the result through
the original tilde map. The argument retains the original T*, even if T* is
not contained in K*V*.

The central-quotient identification is an explicit input produced by the
MarkedModule central-quotient branch; no identification of the whole module or
splitting is assumed. This conditional S₆ branch retains the full proper-K
hypothesis and the original selected component.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.21(6), final paragraph on printed p.924 (PDF p.941).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) {K : Subgroup G}
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

omit [Finite G] [(D.V₁.subgroupOf D.UH).Normal]
  [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- The selected component is the actual alternating subgroup under the
specified S₆ marking, rather than an independently chosen abstract copy. -/
theorem symmetric_six_component_marking (s : Selected D K)
    (hn : (K.subgroupOf D.H).Normal)
    (e : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃*
      Equiv.Perm (Fin 6)) :
    ((starImage D.H K).subgroupOf (starImage D.H K ⊔ starImage D.H D.V)).map
      e.toMonoidHom = alternatingGroup (Fin 6) := by
  let C := starImage D.H K
  let B := C ⊔ starImage D.H D.V
  let Cb := C.subgroupOf B
  let : C.Normal := hn.map (QuotientGroup.mk' (pCore 2 D.H))
    (QuotientGroup.mk'_surjective _)
  let := s.quasisimple
  let c : Cb ≃* C := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect Cb := Group.IsPerfect.ofSurjective (f := c.symm.toMonoidHom) c.symm.surjective
  let : Group.IsPerfect (Cb.map e.toMonoidHom) := Group.IsPerfect.map _
  have hne : C ≠ ⊥ := by
    intro he
    exact s.moved (by change ⁅C, _⁆ = ⊥; rw [he, commutator_bot_left])
  let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hne
  let : Nontrivial Cb := c.symm.injective.nontrivial
  let : Nontrivial (Cb.map e.toMonoidHom) := (e.subgroupMap Cb).injective.nontrivial
  let : (Cb.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ e.surjective
  apply le_antisymm
  · intro x hx
    exact Equiv.Perm.mem_alternatingGroup.mpr
      (Abelianization.commutator_subset_ker
        (Equiv.Perm.sign.comp (Cb.map e.toMonoidHom).subtype)
        (Group.IsPerfect.mem_commutator (g := ⟨x, hx⟩)))
  · exact Equiv.Perm.alternatingGroup_le_of_normal (by norm_num) inferInstance

/-- The original L₁* generates the entire binary module in the S₆ branch.
The kernel of the supplied central projection is retained throughout. -/
theorem symmetric_six_linear_generation
    (s : Selected D K)
    (_proper : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hLK : D.L₁ ≤ K) (hseed : D.Vplus = ⁅D.V, D.L₁⁆)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (S : Subrepresentation
      ((Action.starRepresentation D h).comp (localStar D).subtype))
    [Representation.IsIrreducible S.toRepresentation]
    (hS : S.toSubmodule = Action.seedSpace D)
    (hdim : Module.finrank (ZMod 2) (Action.seedSpace D) = 2)
    (hcomm : Action.seedSpace D = subspaceCommutator (Action.starRepresentation D h)
      (Action.seedSpace D) (starImage D.H D.L₁))
    (e : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃*
      Equiv.Perm (Fin 6))
    (eV : (Action.Space D ⧸ fixedSpace (Action.starRepresentation D h)
      (starImage D.H K)) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (heV : ∀ b : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)),
      ∀ u, centralProjection D h eV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.naturalRepresentation (Fin 6) (e b) (centralProjection D h eV u)) :
    subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H D.L₁) = ⊤ := by
  let ρ : Representation (ZMod 2) (Hstar D.H) (Action.Space D) := Action.starRepresentation D h
  let C := starImage D.H K
  let L := starImage D.H D.L₁
  let B := C ⊔ starImage D.H D.V
  have hCB : C ≤ B := le_sup_left
  let p := centralProjection D h eV
  have hLC : L ≤ C := map_mono (comap_mono hLK)
  have hn := normal_in_H s h hSQ hLK hm
  let : C.Normal := hn.map (QuotientGroup.mk' (pCore 2 D.H))
    (QuotientGroup.mk'_surjective _)
  have hmark := symmetric_six_component_marking D s hn e
  let c : C ≃* alternatingGroup (Fin 6) :=
    ((subgroupOfEquivOfLe (show C ≤ B from le_sup_left)).symm.trans
      (e.subgroupMap (C.subgroupOf B))).trans (MulEquiv.subgroupCongr hmark)
  have hc (k : C) : (c k).val = e ⟨k.val, hCB k.property⟩ := rfl
  let a : alternatingGroup (Fin 6) →* Hstar D.H := C.subtype.comp c.symm.toMonoidHom
  have hac : a.comp c.toMonoidHom = C.subtype := by
    ext k
    exact congrArg Subtype.val (c.symm_apply_apply k)
  have hae (g : alternatingGroup (Fin 6)) :
      e ⟨a g, hCB (c.symm g).property⟩ = g.val :=
    (hc (c.symm g)).symm.trans (congrArg Subtype.val (c.apply_symm_apply g))
  have hp (g : alternatingGroup (Fin 6)) (u : Action.Space D) :
      p (ρ (a g) u) = BinaryPermutation.alternatingNaturalRepresentation (Fin 6) g (p u) := by
    change p (ρ (a g) u) = BinaryPermutation.naturalRepresentation (Fin 6) g.val (p u)
    rw [← hae g]
    exact heV ⟨a g, hCB (c.symm g).property⟩ u
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) (Action.Space D) := ρ.comp a
  let P : σ.IntertwiningMap (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) :=
    p.intertwiningMap_of_isIntertwiningMap _ _ hp
  have hgenC := linear_generation D h s hLK hn hseed
  have hcoin : Coinvariants.ker σ = ⊤ := by
    apply top_unique
    rw [← hgenC]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, u, _, rfl⟩
    have he : a (c ⟨k, hk⟩) = k := congrArg Subtype.val (c.symm_apply_apply ⟨k, hk⟩)
    rw [← he]
    exact Coinvariants.sub_mem_ker (c ⟨k, hk⟩) u
  have hP : Representation.OneCohomology.IsCover P := by
    refine ⟨eV.surjective.comp (Submodule.mkQ_surjective _), ?_, hcoin⟩
    intro u hu g
    have hu' : u ∈ fixedSpace ρ C := (centralProjection_ker D h eV).le hu
    exact hu' ⟨a g, (c.symm g).property⟩
  have hdis : Disjoint (Action.seedSpace D) (fixedSpace ρ C) := by
    rw [← hS]
    apply irreducible_commutator_disjoint_fixedSpace ρ C L (localStar D) S
    · exact le_normalizer_of_normal
    · exact hLC
    · simpa only [hS] using hcomm
  let E := (Action.seedSpace D).map p
  have hdimE : Module.finrank (ZMod 2) E = 2 := by
    rw [image_plane_dimension _ _ (by rwa [centralProjection_ker]), hdim]
  obtain ⟨R, hR⟩ := (starSylow D h).exists_subgroupOf_eq_of_normal C
  let R' := R.mapSurjective (f := c.toMonoidHom) c.surjective
  let J := (L.subgroupOf C).map c.toMonoidHom
  have hJa : J.map a = L := by
    rw [map_map, hac, map_subgroupOf_eq_of_le hLC]
  have hRa : (R' : Subgroup (alternatingGroup (Fin 6))).map a ≤ starImage D.H D.T := by
    change ((R : Subgroup C).map c.toMonoidHom).map a ≤ _
    rw [map_map, hac, hR, subgroupOf_map_subtype]
    exact inf_le_left
  have hJ : IsPPerfect 2 J := by
    have hl := (localStar_residual_twoPerfect D h).of_surjective
      (subgroupOfEquivOfLe hLC).symm.toMonoidHom (subgroupOfEquivOfLe hLC).symm.surjective
    exact hl.of_surjective (c.toMonoidHom.subgroupMap (L.subgroupOf C))
      (c.toMonoidHom.subgroupMap_surjective _)
  have hJne : J ≠ ⊥ := by
    intro hz
    have hzL : L = ⊥ := by rw [← hJa, hz, Subgroup.map_bot]
    exact hm (by change ⁅C, L⁆ = ⊥; rw [hzL, commutator_bot_right])
  have hRn : (R : Subgroup C) ≤ normalizer (L.subgroupOf C : Set C) := by
    rw [hR, ← subgroupOf_normalizer_eq hLC]
    exact comap_mono (starSylow_normalizes_local D h)
  have hR'n : (R' : Subgroup (alternatingGroup (Fin 6))) ≤ normalizer
      (J : Set (alternatingGroup (Fin 6))) :=
    (map_mono hRn).trans (le_normalizer_map _)
  have hE : J ⊔ (R' : Subgroup (alternatingGroup (Fin 6))) ≤
      subspaceStabilizer (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) E := by
    have hlocal : (J ⊔ (R' : Subgroup (alternatingGroup (Fin 6)))).map a ≤ localStar D := by
      rw [Subgroup.map_sup, hJa]
      exact sup_le le_sup_left (hRa.trans le_sup_right)
    apply le_subspaceStabilizer
    rintro g hg _ ⟨u, hu, rfl⟩
    exact ⟨ρ (a g) u,
      (localStar_stabilizes_seed D h (hlocal (mem_map_of_mem a hg)) u).mpr hu, hp g u⟩
  have hgenJ := SixGeneration.cover_generation σ P hP R' J hJ hJne hR'n E hdimE hE
  have hgen := SixGeneration.generated_image σ ρ a (LinearMap.id) Function.surjective_id
    (fun _ _ => rfl) J hgenJ
  rwa [hJa] at hgen

/-- Exact S₆ application of 13.5.21(6), with the original ambient tilde map.
The marked central-quotient construction is the only model identification used. -/
theorem symmetric_six_tilde_generation
    (s : Selected D K)
    (_proper : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hLK : D.L₁ ≤ K) (hseed : D.Vplus = ⁅D.V, D.L₁⁆)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (S : Subrepresentation
      ((Action.starRepresentation D h).comp (localStar D).subtype))
    [Representation.IsIrreducible S.toRepresentation]
    (hS : S.toSubmodule = Action.seedSpace D)
    (hdim : Module.finrank (ZMod 2) (Action.seedSpace D) = 2)
    (hcomm : Action.seedSpace D = subspaceCommutator (Action.starRepresentation D h)
      (Action.seedSpace D) (starImage D.H D.L₁))
    (e : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃*
      Equiv.Perm (Fin 6))
    (eV : (Action.Space D ⧸ fixedSpace (Action.starRepresentation D h)
      (starImage D.H K)) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (heV : ∀ b : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)),
      ∀ u, centralProjection D h eV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.naturalRepresentation (Fin 6) (e b) (centralProjection D h eV u)) :
    D.tilde D.UH = ⁅D.tilde D.UH, D.tilde D.L₁⁆ := by
  apply local_tilde_generation_of_linear D h
  exact symmetric_six_linear_generation D h s _proper hSQ hLK hseed hm S hS hdim hcomm e eV heV

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics
