module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalMaps
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.BarQuotients

/-!
# The original case-one bar and simultaneous parabolic coordinates

In the full-denominator branch, Uγ lies in H_C and hence in the original
Sylow subgroup. It centralizes the seed hyperplane and moves V, so its
natural image contains a transposition. Together with the original A₆
image this proves that the literal centralizer bar is S₆.

Sylow conjugacy aligns the original line and plane simultaneously. Changing
both the natural coordinates and the A₆ actor by that same inner automorphism
preserves the entire LocalSetup. The actual normalizer images then identify
the two residual/Sylow parabolics with H1 and H2. Neither exact marking nor
surjectivity of the natural action is assumed in the case-one application.

Source: Aschbacher--Smith, 13.8.33, printed p.966, and the original flag
in Notation 13.2.1. CaseOne.OriginalComparison applies these results. The
remaining local-plane construction, abelian-span exclusion and final
13.8.33 assembly stay with qt-d-138-a6-endgame-source; earlier ordinary
setup remains with qt-d-138-six-g2-source.
-/

public section
open Subgroup BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
open TransvectionQuotients.FourLocalFactors
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
local notation "r" => naturalRepresentation (Fin 6)

noncomputable def recoordinate (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (g : Equiv.Perm (Fin 6)) : LocalSetup T L V V₁ V₂ V₃ M G₁ :=
  { d with
    local_quotient := d.local_quotient.trans (MulAut.conjNormal g)
    coordinate := d.coordinate.trans
      (LinearEquiv.ofBijective (r g) ((naturalRepresentation (Fin 6)).apply_bijective g)).toAddEquiv.toMultiplicative
    conjugation := by
      intro l v
      change r g (d.coordinate (V.normalizerMonoidHom _ v)).toAdd =
        r (g * (d.local_quotient (QuotientGroup.mk' (centralCore L) l)).val * g⁻¹)
          (r g (d.coordinate v).toAdd)
      rw [d.conjugation]
      change r g (r (d.local_quotient (QuotientGroup.mk' (centralCore L) l)).val _) = _
      simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one] }

theorem recoordinate_permutation (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (g : Equiv.Perm (Fin 6)) (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    Section07.NaturalAction.permutation (localNaturalSetup (recoordinate d g)) x =
      g * Section07.NaturalAction.permutation (localNaturalSetup d) x * g⁻¹ := by
  apply naturalRepresentation_injective (Fin 6) (by decide)
  apply LinearMap.ext
  intro w
  obtain ⟨v,hv⟩ := (recoordinate d g).coordinate.surjective (Multiplicative.ofAdd w)
  have hv' : r g (d.coordinate v).toAdd = w := hv
  rw [← hv']
  have hnew := Section07.NaturalAction.conjugation (localNaturalSetup (recoordinate d g)) x v
  have hold := Section07.NaturalAction.conjugation (localNaturalSetup d) x v
  change r g (d.coordinate (V.normalizerMonoidHom _ v)).toAdd = _ at hnew
  change (d.coordinate (V.normalizerMonoidHom _ v)).toAdd =
    r (Section07.NaturalAction.permutation (localNaturalSetup d) x) (d.coordinate v).toAdd at hold
  change r g (d.coordinate (V.normalizerMonoidHom _ v)).toAdd =
    r (Section07.NaturalAction.permutation (localNaturalSetup (recoordinate d g)) x)
      (r g (d.coordinate v).toAdd) at hnew
  rw [hold] at hnew
  rw [← hnew]
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem recoordinate_image (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (g : Equiv.Perm (Fin 6)) (B : Subgroup G) :
    Section07.NaturalAction.image (localNaturalSetup (recoordinate d g)) B =
      (Section07.NaturalAction.image (localNaturalSetup d) B).map (r g) := by
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨(d.coordinate v).toAdd,⟨v,hv,rfl⟩,rfl⟩
  · rintro ⟨u,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨v,hv,rfl⟩

theorem exists_aligned_coordinates (d : LocalSetup T L V V₁ V₂ V₃ M G₁) :
    ∃ g : Equiv.Perm (Fin 6),
      Section07.NaturalAction.image (localNaturalSetup (recoordinate d g)) V₁ = canonicalLine ∧
      Section07.NaturalAction.image (localNaturalSetup (recoordinate d g)) V₂ = canonicalPlane := by
  let n := localNaturalSetup d
  let π := Section07.NaturalAction.permutation n
  let Q := (T.subtype (show (T : Subgroup G) ≤ L ⊔ T from le_sup_right)).mapSurjective
    π.rangeRestrict_surjective
  have hQ : (Q : Subgroup π.range).map π.range.subtype =
      ((T : Subgroup G).subgroupOf (L ⊔ T)).map π := by
    rw [Sylow.coe_mapSurjective, map_map, Sylow.coe_subtype]
    rfl
  obtain ⟨g,hg⟩ := TransvectionParabolic.EarlierCore.PlaneGeometry.exists_conjugate_T0_le
    π.range (Section07.NaturalAction.alternating_le_range n) Q
  let F := LinearEquiv.ofBijective (r g.val⁻¹) ((naturalRepresentation (Fin 6)).apply_bijective g.val⁻¹)
  have hstable (B : Subgroup G) (hB : (T : Subgroup G) ≤ normalizer (B : Set G)) :=
    TransvectionParabolic.EarlierCore.PlaneGeometry.aligned_invariant π.range Q g hg
      (Section07.NaturalAction.image n B)
      (hQ.symm ▸ Section07.NaturalAction.image_stable n B hB)
  refine ⟨g.val⁻¹,?_,?_⟩
  · rw [recoordinate_image]
    exact canonicalLine_unique _ ((F.finrank_map_eq _).trans
      (Section07.NaturalAction.image_dim n V₁
        (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 d.line_card))
      (hstable V₁ d.line_stable)
  · rw [recoordinate_image]
    exact canonicalPlane_unique _ ((F.finrank_map_eq _).trans
      (Section07.NaturalAction.image_dim n V₂ (d.plane_le_seed.trans d.seed_le) 2 d.plane_card))
      (hstable V₂ d.plane_stable)


private theorem mem_image_iff (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (B : Subgroup G) (v : V) :
    (d.coordinate v).toAdd ∈ Section07.NaturalAction.image (localNaturalSetup d) B ↔ v.val ∈ B := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact (d.coordinate.injective he) ▸ hw
  · exact fun hv => ⟨v,hv,rfl⟩

theorem original_normalizer_image (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hs : Function.Surjective (Section07.NaturalAction.permutation (localNaturalSetup d)))
    (B : Subgroup G) (hBV : B ≤ V) :
    (((L ⊔ (T : Subgroup G)) ⊓ normalizer (B : Set G)).subgroupOf
      (L ⊔ (T : Subgroup G))).map
      (Section07.NaturalAction.permutation (localNaturalSetup d)) =
        subspaceStabilizer r (Section07.NaturalAction.image (localNaturalSetup d) B) := by
  let n := localNaturalSetup d
  have hc (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V) :
      (d.coordinate (V.normalizerMonoidHom ⟨x.val,d.normalizes_V x.property⟩ v)).toAdd =
        r (Section07.NaturalAction.permutation n x) (d.coordinate v).toAdd :=
    Section07.NaturalAction.conjugation n x v
  have hiff (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
      x.val ∈ normalizer (B : Set G) ↔ Section07.NaturalAction.permutation n x ∈
        subspaceStabilizer r (Section07.NaturalAction.image n B) := by
    constructor
    · intro hx w
      obtain ⟨v,hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
      have hv' : (d.coordinate v).toAdd = w := hv
      rw [← hv', ← hc x v]
      exact (mem_image_iff d B _).trans
        (((mem_normalizer_iff.mp hx) v.val).symm.trans (mem_image_iff d B v).symm)
    · intro hx
      apply mem_normalizer_iff.mpr
      intro v
      constructor
      · intro hv
        have hm : (d.coordinate ⟨v,hBV hv⟩).toAdd ∈ Section07.NaturalAction.image n B :=
          (mem_image_iff d B _).mpr hv
        have hh := (hx _).mpr hm
        rw [← hc x ⟨v,hBV hv⟩] at hh
        exact (mem_image_iff d B _).mp hh
      · intro hv
        have hvV : v ∈ V := (mem_normalizer_iff.mp (d.normalizes_V x.property) v).mpr (hBV hv)
        let u : V := ⟨v,hvV⟩
        have hm : (d.coordinate (V.normalizerMonoidHom ⟨x.val,d.normalizes_V x.property⟩ u)).toAdd ∈
            Section07.NaturalAction.image n B := (mem_image_iff d B _).mpr hv
        rw [hc x u] at hm
        exact (mem_image_iff d B u).mp ((hx _).mp hm)
  ext b
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hiff x).mp hx.2
  · intro hb
    obtain ⟨x,rfl⟩ := hs b
    exact ⟨x,⟨x.property,(hiff x).mpr hb⟩,rfl⟩

/-- Both literal parabolics acquire their standard markings under one
inner change of the original natural coordinates. -/
theorem exists_original_parabolic_coordinates
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) (hH : H = G₁)
    (eb : (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (L₂ : Subgroup G)
    (hL₂ : L₂ = BarQuotients.sourceResidual L (T : Subgroup G) V₂) :
    ∃ d' : LocalSetup T L V V₁ V₂ V₃ M G₁,
      ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf (L ⊔ (T : Subgroup G))).map
        (Section07.NaturalAction.permutation (localNaturalSetup d'))) = H1 ∧
      (((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
        (Section07.NaturalAction.permutation (localNaturalSetup d'))) = H2 := by
  obtain ⟨g,hg₁,hg₂⟩ := exists_aligned_coordinates d
  let d' := recoordinate d g
  have hs : Function.Surjective (Section07.NaturalAction.permutation (localNaturalSetup d)) := by
    intro b
    obtain ⟨x,hx⟩ := (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).rangeRestrict_surjective
      ((original_bar_equiv d eb).symm b)
    refine ⟨x,?_⟩
    rw [← original_bar_equiv_apply d eb x,hx,MulEquiv.apply_symm_apply]
  have hs' : Function.Surjective (Section07.NaturalAction.permutation (localNaturalSetup d')) := by
    intro b
    obtain ⟨x,hx⟩ := hs (g⁻¹*b*g)
    refine ⟨x,?_⟩
    rw [recoordinate_permutation,hx]
    group
  have hR : L₂ ⊔ (T : Subgroup G) = (L ⊔ (T : Subgroup G)) ⊓ normalizer (V₂ : Set G) := by
    let P := (L ⊔ (T : Subgroup G)) ⊓ normalizer (V₂ : Set G)
    have hTP : (T : Subgroup G) ≤ P := le_inf le_sup_right d.plane_stable
    have hh := congrArg (fun A : Subgroup P => A.map P.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hTP))
    rw [hL₂]
    change (pResidual 2 P).map P.subtype ⊔ (T : Subgroup G) = P
    simpa only [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP,
      ← MonoidHom.range_eq_map,range_subtype] using hh
  have hHN : H = normalizer (V₁ : Set G) := hH.trans d.first_normalizer
  refine ⟨d',?_,?_⟩
  · rw [hHN,original_normalizer_image d' hs' V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)),hg₁]
    ext x
    exact (mem_stabilizer_iff_map _ _).trans (canonicalLine_stabilizer x)
  · rw [hR,original_normalizer_image d' hs' V₂ (d.plane_le_seed.trans d.seed_le),hg₂]
    ext x
    exact (mem_stabilizer_iff_map _ _).trans (canonicalPlane_stabilizer x)


/-- In case one, Uγ centralizes the seed hyperplane but moves V. Its
realized transposition makes the original natural image the whole S₆. -/
theorem full_denominators_natural_surjective
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) :
    Function.Surjective (Section07.NaturalAction.permutation (localNaturalSetup d)) := by
  let π := Section07.NaturalAction.permutation (localNaturalSetup d)
  obtain ⟨hc,hm,_⟩ := ComponentSieve.SixAndG2.Overgroup.full_denominators_commutator d h c hDH hDg
  have hg := local_earlierGeometry d h c
  have hUgH : c.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans hg.Vgamma_H
  have hUgC : c.Ugamma V₃ ≤ centralizer (Source.UH H V₃ : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  have hUgQ : c.Ugamma V₃ ≤ Source.QH H := by
    apply le_trans _ h.kernel_UH_eq_QH.le
    intro x hx
    exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hUgH hx,fun u hu => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hUgC hx u hu)]
      exact V₁.one_mem⟩
  have hUgP := hUgQ.trans (h.QH_le_T.trans (show (T : Subgroup G) ≤ L ⊔ T from le_sup_right))
  obtain ⟨t,ht,htf⟩ := Section07.source_hyperplane_fixer (localNaturalSetup d)
  have htR : t ∈ π.range := by
    by_contra hno
    have hz : c.Ugamma V₃ ≤ centralizer (V : Set G) := by
      intro x hx
      let y : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨x,hUgP hx⟩
      apply (Section07.permutation_eq_one_iff (localNaturalSetup d) y).mp
      rcases htf y ((centralizer_le (le_conjugateSpanBy V₃ H)) (hUgC hx)) with he | he
      · exact he
      · exact (hno ⟨y,he⟩).elim
    have he : V₁ = ⊥ := hm.symm.trans (by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hz)
    have hcard := d.line_card
    rw [he,card_bot] at hcard
    contradiction
  apply MonoidHom.range_eq_top.mp
  have hd : π.range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using
      index_dvd_of_le (Section07.NaturalAction.alternating_le_range (localNaturalSetup d))
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact index_eq_one.mp hi
  have he := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
  rw [he] at htR
  have hs : Equiv.Perm.sign t = 1 := htR
  rw [ht.sign_eq] at hs
  contradiction

/-- Construct the source S₆ bar itself; no symmetric image or parabolic
marking is an extra premise. -/
theorem exists_full_denominators_bar_equiv
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) :
    Nonempty ((barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).range ≃* Equiv.Perm (Fin 6)) := by
  let := barKernel_normal (L ⊔ (T : Subgroup G)) V d.normalizes_V
  have hk : (Section07.NaturalAction.permutation (localNaturalSetup d)).ker =
      barKernel (L ⊔ (T : Subgroup G)) V := by
    ext x
    exact Section07.permutation_eq_one_iff (localNaturalSetup d) x
  exact ⟨(barEquivImage (L ⊔ (T : Subgroup G)) V d.normalizes_V).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (full_denominators_natural_surjective d h c hDH hDg)))⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
