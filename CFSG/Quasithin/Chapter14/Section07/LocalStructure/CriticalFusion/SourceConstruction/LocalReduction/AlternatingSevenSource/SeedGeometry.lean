module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Seed
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.Generation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceFixedLines
public import Theory.GroupAction.FourPerfectOrbit

/-!
# The original seed and flag line in a proper local quotient

Seed separation makes every proper equivariant quotient injective on the
original binary seed plane. Its flag line consequently has dimension one
and is fixed by the original Sylow. The actual point residual is
two-perfect and moves the seed fully, so its three nonzero image vectors
form one orbit. These facts retain the quotient map and apply equally to
the four-, six-, and eight-dimensional alternatives of 14.7.50.

Source: Aschbacher–Smith 14.7.2(1), 14.7.48(2), and 14.7.50,
printed pp.1043 and 1064–1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source
universe u v w
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type v} {X : Type w}
  [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
  {I : Subgroup G} {ρ : Representation (ZMod 2) I W}
  {σ : Representation (ZMod 2) I X}

/-- No nonzero seed vector is lost in a proper invariant quotient. -/
theorem local_quotient_seed_disjoint
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤) :
    Disjoint (c.imageSpace V) p.toLinearMap.ker := by
  apply Submodule.disjoint_def.mpr
  intro w hw hk
  obtain ⟨v,hv,rfl⟩ := (c.mem_imageSpace_iff V w).mp hw
  have hs := local_seed_intersection h I hI c p.toLinearMap.ker (by
    intro g w hw
    change p (ρ g w) = 0
    rw [p.isIntertwining,show p w = 0 from hw,map_zero]) hp
  exact (c.coordinates_eq_one_iff v).mpr ((hs v hv).mp hk)

private theorem mapped_seed_subspace_finrank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (B : Subgroup G) (hB : B ≤ V) :
    Module.finrank (ZMod 2) ((c.imageSpace B).map p.toLinearMap) =
      Module.finrank (ZMod 2) (c.imageSpace B) := by
  let : Finite W := Finite.of_surjective (fun v : F.UH I => (c.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let E := c.imageSpace B
  let f := p.toLinearMap.comp E.subtype
  have hd : Disjoint E p.toLinearMap.ker :=
    (local_quotient_seed_disjoint h hI c p hp).mono_left (c.imageSpace_mono hB)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact (Submodule.disjoint_def.mp hd) x.val x.property hx
  have hr : LinearMap.range f = E.map p.toLinearMap := by
    rw [LinearMap.range_comp,Submodule.range_subtype]
  exact hr ▸ LinearMap.finrank_range_of_inj hf

/-- The original seed remains a plane on every proper local quotient. -/
theorem local_quotient_seed_finrank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤) :
    Module.finrank (ZMod 2) ((c.imageSpace V).map p.toLinearMap) = 2 := by
  rw [mapped_seed_subspace_finrank h hI c p hp V le_rfl]
  apply c.imageSpace_finrank_of_index V (le_conjugateSpanBy V I) 2
  have hc := relIndex_mul_card_of_le (F.le_seed 1)
  have hV : Nat.card V = 8 := by
    simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
  rw [F.card 1 (by decide),hV] at hc
  norm_num at hc ⊢
  omega

/-- The image of the original order-four flag plane is a binary line. -/
theorem local_quotient_plane_finrank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤) :
    Module.finrank (ZMod 2) ((c.imageSpace (F.Vi 2)).map p.toLinearMap) = 1 := by
  rw [mapped_seed_subspace_finrank h hI c p hp (F.Vi 2) (F.le_seed 2)]
  apply c.imageSpace_finrank_of_index (F.Vi 2)
    ((F.le_seed 2).trans (le_conjugateSpanBy V I)) 1
  have hc := relIndex_mul_card_of_le (F.monotone (by decide : 1 ≤ 2))
  rw [F.card 1 (by decide),F.card 2 (by decide)] at hc
  norm_num at hc ⊢
  omega

/-- The original Sylow fixes the quotient flag line pointwise. -/
theorem local_quotient_plane_sylow_fixed
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (t : I) (ht : (t : G) ∈ (T : Subgroup G))
    (x : X) (hx : x ∈ (c.imageSpace (F.Vi 2)).map p.toLinearMap) : σ t x = x := by
  obtain ⟨w,hw,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := (c.mem_imageSpace_iff (F.Vi 2) w).mp hw
  change σ t (p (c.coordinates v).toAdd) = p (c.coordinates v).toAdd
  rw [←p.isIntertwining]
  rw [flag_plane_fixed ρ c ((F.le_seed 2).trans (le_conjugateSpanBy V I))
    (F.monotone (by decide : 1 ≤ 2)) (by simpa using F.card 1 (by decide))
    (by simpa using F.card 2 (by decide)) t (F.invariant 2 ht) v hv]

/-- The literal point residual is transitive on the three nonzero vectors
of the quotient seed, with the same ambient actor and quotient map. -/
theorem local_quotient_seed_transitive
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ)
    (x : X) (hx : x ∈ (c.imageSpace V).map p.toLinearMap) (hx0 : x ≠ 0)
    (y : X) (hy : y ∈ (c.imageSpace V).map p.toLinearMap) (hy0 : y ≠ 0) :
    ∃ a : F.Li L 1, σ (inclusion (F.Li_one_le_of_mem_Hz hI) a) x = y := by
  let : Finite W := Finite.of_surjective (fun v : F.UH I => (c.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let E := c.imageSpace V
  let j := inclusion (F.Li_one_le_of_mem_Hz hI)
  let τ := ρ.comp j
  have hn : F.Li L 1 ≤ normalizer (V : Set G) :=
    (F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes)
  have hs (a : F.Li L 1) : E ≤ E.comap (τ a) :=
    c.imageSpace_apply_mem V (j a) (hn a.property)
  let κ := Representation.subrepresentation τ E hs
  have hd : Module.finrank (ZMod 2) E = 2 := by
    apply c.imageSpace_finrank_of_index V (le_conjugateSpanBy V I) 2
    have hc := relIndex_mul_card_of_le (F.le_seed 1)
    have hV : Nat.card V = 8 := by
      simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    rw [F.card 1 (by decide),hV] at hc
    norm_num at hc ⊢
    omega
  have hκ : ∃ a, κ a ≠ 1 := by
    by_contra! ht
    have hc : ⁅F.Li L 1,V⁆ ≤ F.Vi 1 := by
      apply commutator_le.mpr
      intro a ha b hb
      let u : F.UH I := ⟨b,le_conjugateSpanBy V I hb⟩
      have hu : (c.coordinates u).toAdd ∈ E :=
        (c.mem_imageSpace_iff V _).mpr ⟨u,hb,rfl⟩
      have hf := congrArg Subtype.val (LinearMap.congr_fun (ht ⟨a,ha⟩) ⟨_,hu⟩)
      let v : F.UH I := ⟨a*b*a⁻¹,
        (mem_normalizer_iff.mp (c.normalized ((F.Li_one_le_of_mem_Hz hI) ha)) b).mp u.property⟩
      have he : c.coordinates v = c.coordinates u := (c.equivariant (j ⟨a,ha⟩) u).trans hf
      exact (c.coordinates_eq_one_iff (v*u⁻¹)).mp (by rw [map_mul,map_inv,he,mul_inv_cancel])
    rw [commutator_comm,←seed_commutator h F] at hc
    have hc' := card_le_of_le hc
    have hV : Nat.card V = 8 := by
      simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    rw [hV,F.card 1 (by decide)] at hc'
    norm_num at hc'
  have hperfect : IsPPerfect 2 (F.Li L 1) := by
    exact ResidualNormalizer.Li_twoPerfect
  obtain ⟨x',hx',rfl⟩ := hx
  obtain ⟨y',hy',rfl⟩ := hy
  have hx'0 : (⟨x',hx'⟩ : E) ≠ 0 := by
    intro he
    apply hx0
    rw [show x' = 0 from congrArg Subtype.val he,map_zero]
  have hy'0 : (⟨y',hy'⟩ : E) ≠ 0 := by
    intro he
    apply hy0
    rw [show y' = 0 from congrArg Subtype.val he,map_zero]
  obtain ⟨a,ha⟩ := nonzero_orbit_of_twoPerfect_plane hperfect hd κ
    hκ ⟨x',hx'⟩ hx'0 ⟨y',hy'⟩ hy'0
  refine ⟨a,?_⟩
  change σ (j a) (p x') = p y'
  rw [←p.isIntertwining]
  exact congrArg p (congrArg Subtype.val ha)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
