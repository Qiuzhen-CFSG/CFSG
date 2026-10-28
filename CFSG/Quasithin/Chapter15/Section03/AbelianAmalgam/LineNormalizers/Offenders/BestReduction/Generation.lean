module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Maximum
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.PairedSection
public import Theory.Representation.BinaryOffender.SmallRank


/-!
# A central-line route to generation of the Thompson image

The central-line calculation compares every subgroup of a quotient image.
For its preimage X, let L be the preimage of its fixed space, F the fixed space
of the maximum elementary actor, and K the pointwise kernel of X on L.
Displacements embed X/K in Hom(L/F, ker π). When ker π is a central line,
this bounds the lost actor rank by dim(L/F). Two equivariant copies of L
then give twice this gain in fixed dimension, proving the full weight
comparison. Maximum elementary order supplies the doubled weight bound;
it is not a hypothesis of the maximum-family or generation theorems.

The conditional `DoubledCentralLift` concerns the WHOLE module U. It has not
been constructed from the source's marked geometry. `PairedSection` only
splits U/E and cannot be substituted for this stronger input. In particular,
C-invariance of the raw τ-fixed space is not asserted here. Thus this module
does not yet discharge the best-offender inference on printed p.1154.

The final lemma preserves the literal image of J(S) and its containment in
the image of S, inside the very same Thompson actor I.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Definitions
B.1.2–3, printed p.68, and the proof of 15.3.67, printed pp.1153–1154.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction
variable {G H V W : Type*} [Group G] [Finite G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem restriction_rank_bound
    (ρ : Representation (ZMod 2) G V) (X : Subgroup G)
    [IsElementaryAbelian 2 X] (L F Z : Submodule (ZMod 2) V)
    (hXL : X ≤ subspaceStabilizer ρ L) (hZL : Z ≤ L)
    (hF : F ≤ fixedSpace ρ X)
    (hdisp : ∀ x ∈ X, ∀ v ∈ L, ρ x v - v ∈ Z) :
    rank X ≤ rank (subspaceKernel ρ L X) +
      Module.finrank (ZMod 2) (L ⧸ F.comap L.subtype) * Module.finrank (ZMod 2) Z := by
  let σ := subspaceImageRepresentation ρ L
  have hfixed : F.comap L.subtype ≤ fixedSpace σ (restrictedSubgroup ρ L X) := by
    intro v hv
    rintro ⟨_, g, hg, rfl⟩
    apply Subtype.ext
    exact hF hv ⟨g, hg⟩
  have hd : ∀ g ∈ restrictedSubgroup ρ L X, ∀ v : L,
      σ g v - v ∈ Z.comap L.subtype := by
    rintro _ ⟨g, hg, rfl⟩ v
    exact hdisp g hg v v.property
  have hr := rank_le_fixed_codim_mul_displacement_dim σ
    (subspaceImageRepresentation_injective ρ L) (restrictedSubgroup ρ L X)
    (F.comap L.subtype) (Z.comap L.subtype) hfixed hd
  rw [(Submodule.comapSubtypeEquivOfLe hZL).finrank_eq] at hr
  have hk := rank_subspaceKernel_add_image ρ L X hXL
    (IsElementaryAbelian.isPGroup 2 X)
  omega

/-- A central line quotient of a representation with doubled weight maximality
has the full best-offender comparison, not only its trivial-subgroup case. -/
private theorem central_line_quotient_weight_comparison
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) H W)
    (q : G →* H) (π : V →ₗ[ZMod 2] W) (hπ : Function.Surjective π)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (heq : ∀ a ∈ A, ∀ v, π (ρ a v) = σ (q a) (π v))
    (hcentral : π.ker ≤ fixedSpace ρ A)
    (hline : Module.finrank (ZMod 2) π.ker ≤ 1)
    (hdouble : ∀ K ≤ A, rank K + 2 * Module.finrank (ZMod 2) (fixedSpace ρ K) ≤
      rank A + 2 * Module.finrank (ZMod 2) (fixedSpace ρ A))
    (B : Subgroup H) (hBA : B ≤ A.map q) :
    weight σ B ≤ weight σ (A.map q) := by
  let X := A ⊓ B.comap q
  let L := (fixedSpace σ B).comap π
  let F := fixedSpace ρ A
  have hXA : X ≤ A := inf_le_left
  let : IsElementaryAbelian 2 X := IsElementaryAbelian.of_le hXA
  have hXq : X.map q = B := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := hBA hb
      exact ⟨a, ⟨ha, hb⟩, rfl⟩
  have hFL : F ≤ L := by
    intro v hv b
    obtain ⟨a, ha, hab⟩ := hBA b.property
    have hh := heq a ha v
    rw [show ρ a v = v from hv ⟨a, ha⟩, hab] at hh
    exact hh.symm
  have hZL : π.ker ≤ L := by
    intro v hv
    change π v ∈ fixedSpace σ B
    rw [LinearMap.mem_ker.mp hv]
    exact (fixedSpace σ B).zero_mem
  have hd : ∀ x ∈ X, ∀ v ∈ L, ρ x v - v ∈ π.ker := by
    intro x hx v hv
    rw [LinearMap.mem_ker, map_sub, heq x hx.1]
    exact sub_eq_zero.mpr (hv ⟨q x, hx.2⟩)
  have hXL : X ≤ subspaceStabilizer ρ L := by
    apply le_subspaceStabilizer
    intro x hx v hv
    have hh := L.add_mem (hZL (hd x hx v hv)) hv
    simpa only [sub_add_cancel] using hh
  let K := subspaceKernel ρ L X
  have hKX : K ≤ X := subspaceKernel_le ρ L X
  have hKL : L ≤ fixedSpace ρ K := le_fixedSpace_subspaceKernel ρ L X
  have hr := restriction_rank_bound ρ X L F π.ker hXL hZL
    (fun v hv x => hv ⟨x, hXA x.property⟩) hd
  have hmul := Nat.mul_le_mul_left
    (Module.finrank (ZMod 2) (L ⧸ F.comap L.subtype)) hline
  simp only [mul_one] at hmul
  have hn := (F.comap L.subtype).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe hFL).finrank_eq] at hn
  have hm := hdouble K (hKX.trans hXA)
  have hdim := Submodule.finrank_mono hKL
  have hrank : rank X + Module.finrank (ZMod 2) L ≤
      rank A + Module.finrank (ZMod 2) F := by
    change rank X ≤ rank K + _ at hr
    change rank K + 2 * Module.finrank (ZMod 2) (fixedSpace ρ K) ≤
      rank A + 2 * Module.finrank (ZMod 2) F at hm
    omega
  let p : L →ₗ[ZMod 2] fixedSpace σ B :=
    (π.domRestrict L).codRestrict _ (fun v => v.property)
  have hp : Function.Surjective p := by
    intro w
    obtain ⟨v, hv⟩ := hπ w
    exact ⟨⟨v, by change π v ∈ fixedSpace σ B; rw [hv]; exact w.property⟩,
      Subtype.ext hv⟩
  have he : p.ker ≃ₗ[ZMod 2] π.ker :=
    { toFun := fun v => ⟨v.val, congrArg Subtype.val v.property⟩
      invFun := fun v => ⟨⟨v, hZL v.property⟩, Subtype.ext v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hpdim := p.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp, finrank_top, he.finrank_eq] at hpdim
  let r : F →ₗ[ZMod 2] fixedSpace σ (A.map q) :=
    (π.domRestrict F).codRestrict _ (by
      intro v
      rintro ⟨_, a, ha, rfl⟩
      exact (heq a ha v).symm.trans (congrArg π (v.property ⟨a, ha⟩)))
  have hrker : r.ker ≃ₗ[ZMod 2] π.ker :=
    { toFun := fun v => ⟨v.val, congrArg Subtype.val v.property⟩
      invFun := fun v => ⟨⟨v, hcentral v.property⟩, Subtype.ext v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrdim := r.finrank_range_add_finrank_ker
  rw [hrker.finrank_eq] at hrdim
  have hrle := r.range.finrank_le
  have hAr := rank_kernel_add_image A q
  have hXr := rank_kernel_add_image X q
  have hk : X ⊓ q.ker = A ⊓ q.ker := by
    apply le_antisymm
    · exact inf_le_inf hXA le_rfl
    · intro a ha
      refine ⟨⟨ha.1, ?_⟩, ha.2⟩
      change q a ∈ B
      rw [ha.2]
      exact B.one_mem
  rw [hk, hXq] at hXr
  unfold weight
  omega


/-- Maximum elementary order controls every subgroup K, including those which
do not contain A ∩ U. Adjoin A ∩ U before applying the replacement comparison;
this changes no U-fixed vectors. -/
theorem maximum_fixed_weight_comparison_all
    (S U A K : Subgroup G) [IsElementaryAbelian 2 U]
    (hUS : U ≤ S) (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (hKA : K ≤ A) :
    rank K + rank (U ⊓ centralizer (K : Set G)) ≤
      rank A + rank (U ⊓ centralizer (A : Set G)) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let X := K ⊔ (A ⊓ U)
  have hXA : X ≤ A := sup_le hKA inf_le_left
  have heq : U ⊓ centralizer (X : Set G) = U ⊓ centralizer (K : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left U (centralizer_le (show K ≤ X from le_sup_left))
    · apply le_inf inf_le_left
      apply le_centralizer_iff.mpr
      apply sup_le
      · exact le_centralizer_iff.mp inf_le_right
      · exact inf_le_right.trans (le_centralizer_iff.mp
          (inf_le_left.trans U.le_centralizer))
  have hm := maximum_fixed_weight_comparison S U A X hUS hA hXA le_sup_right
  rw [heq] at hm
  have hr : rank K ≤ rank X := Nat.log_mono_right (Nat.card_le_card_of_injective (Subgroup.inclusion (show K ≤ X from le_sup_left))
      (Subgroup.inclusion_injective _))
  omega

/-- For a maximum member, the core doubling identity identifies exactly which
of its two action images are nontrivial. A maximum member contained in the
core centralizes U. This does not assert that its intersection with the core
centralizes U when its quotient image is nontrivial. -/
theorem maximum_images_nontrivial_iff
    (S U A Q : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] [Q.Normal]
    (hUS : U ≤ S) (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G)) (hkerQ : A ⊓ f.ker ≤ Q)
    (hcore : quotientRank U (U ⊓ centralizer ((A ⊓ Q : Subgroup G) : Set G)) =
      2 * rank ((A ⊓ Q).map f)) :
    A.map f ≠ ⊥ ↔ A.map (QuotientGroup.mk' Q) ≠ ⊥ := by
  let : Finite H := Finite.of_surjective f hf
  constructor
  · intro hn hzero
    have hAQ : A ≤ Q := by
      simpa only [QuotientGroup.ker_mk'] using
        (Subgroup.map_eq_bot_iff A).mp hzero
    rw [inf_eq_left.mpr hAQ] at hcore
    have hb := (maximum_image_isBestOffender S U A hUS hA f hf hker hn).isOffender _
    rw [quotientRank_eq_fixedCodim U f hf hker A] at hcore
    have hp := hb.1.rank_pos
    have hi := hb.2
    omega
  · intro hn hzero
    apply hn
    apply (Subgroup.map_eq_bot_iff A).mpr
    rw [QuotientGroup.ker_mk']
    exact (le_inf le_rfl ((Subgroup.map_eq_bot_iff A).mp hzero)).trans hkerQ

private theorem double_fixed_finrank {D Z : Type*} [Group D]
    [AddCommGroup Z] [Module (ZMod 2) Z] [FiniteDimensional (ZMod 2) Z]
    (ρ : Representation (ZMod 2) D Z) (τ : Representation (ZMod 2) D V)
    (e : Z ≃ₗ[ZMod 2] V × V)
    (he : ∀ g v, e (ρ g v) = (τ g (e v).1, τ g (e v).2))
    (K : Subgroup D) :
    Module.finrank (ZMod 2) (fixedSpace ρ K) =
      2 * Module.finrank (ZMod 2) (fixedSpace τ K) := by
  let l : fixedSpace ρ K ≃ₗ[ZMod 2] (fixedSpace τ K) × (fixedSpace τ K) :=
    { toFun := fun v =>
        (⟨(e v).1, fun g => by
          have hh := congrArg Prod.fst (he g v)
          rw [show ρ g v = v from v.property g] at hh
          exact hh.symm⟩,
         ⟨(e v).2, fun g => by
          have hh := congrArg Prod.snd (he g v)
          rw [show ρ g v = v from v.property g] at hh
          exact hh.symm⟩)
      invFun := fun v => ⟨e.symm (v.1, v.2), fun g => by
        apply e.injective
        change e (ρ g (e.symm (v.1, v.2))) = e (e.symm (v.1, v.2))
        rw [he, e.apply_symm_apply]
        exact Prod.ext (v.1.property g) (v.2.property g)⟩
      left_inv := fun v => Subtype.ext (e.symm_apply_apply v)
      right_inv := fun v => by
        apply Prod.ext <;> apply Subtype.ext
        · exact congrArg Prod.fst (e.apply_symm_apply (v.1, v.2))
        · exact congrArg Prod.snd (e.apply_symm_apply (v.1, v.2))
      map_add' := fun v w => by
        apply Prod.ext <;> apply Subtype.ext
        · exact congrArg Prod.fst (e.map_add v w)
        · exact congrArg Prod.snd (e.map_add v w)
      map_smul' := fun c v => by
        apply Prod.ext <;> apply Subtype.ext
        · exact congrArg Prod.fst (e.map_smul c v)
        · exact congrArg Prod.snd (e.map_smul c v) }
  simpa only [Module.finrank_prod, two_mul] using l.finrank_eq

/-- A sufficient geometric lift for the transfer: the WHOLE internal module,
restricted to this particular maximum elementary subgroup, is two copies of a
central-line extension of the marked first summand. This is additional data;
it is not supplied by `PairedSection`, which only splits the quotient. -/
structure DoubledCentralLift (U A Q : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 U] [Q.Normal]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G))
    (σ : Representation (ZMod 2) (G ⧸ Q) W) where
  half : Representation (ZMod 2) A V
  coordinates : Additive U ≃ₗ[ZMod 2] V × V
  intertwines : ∀ a : A, ∀ v,
    coordinates (Representation.NormalElementaryQuotient.representation U f hf hker (f a) v) =
      (half a (coordinates v).1, half a (coordinates v).2)
  projection : V →ₗ[ZMod 2] W
  surjective : Function.Surjective projection
  quotient_action : ∀ a : A, ∀ v,
    projection (half a v) = σ (QuotientGroup.mk' Q a) (projection v)
  central : projection.ker ≤ half.invariants
  line : Module.finrank (ZMod 2) projection.ker ≤ 1

/-- With an actual doubled central lift, maximum elementary order proves every
weight comparison on the marked quotient. No bestness or weight bound is input. -/
theorem maximum_image_best_of_doubledCentralLift
    (S U A Q : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] [Q.Normal]
    (hUS : U ≤ S) (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G))
    (σ : Representation (ZMod 2) (G ⧸ Q) W)
    (d : DoubledCentralLift (V := V) U A Q f hf hker σ)
    (hne : A.map (QuotientGroup.mk' Q) ≠ ⊥) :
    IsBestOffender σ (A.map (QuotientGroup.mk' Q)) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let ρ := Representation.NormalElementaryQuotient.representation U f hf hker
  let r := (ρ.comp f).comp A.subtype
  have hfixed (K : Subgroup A) :
      rank (U ⊓ centralizer (K.map A.subtype : Set G)) =
        2 * Module.finrank (ZMod 2) (fixedSpace d.half K) := by
    have he := double_fixed_finrank r d.half d.coordinates d.intertwines K
    rw [fixedSpace_comp_map, fixedSpace_comp_map] at he
    rw [rank, ← Nat.card_congr
      (Representation.NormalElementaryQuotient.fixedSpaceEquiv U f hf hker
        (K.map A.subtype)),
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      Nat.log_pow Nat.one_lt_two]
    exact he
  have htop : (⊤ : Subgroup A).map A.subtype = A := by
    ext a
    constructor
    · rintro ⟨x, _, rfl⟩
      exact x.property
    · intro ha
      exact ⟨⟨a, ha⟩, trivial, rfl⟩
  have hdouble (K : Subgroup A) (_ : K ≤ ⊤) :
      rank K + 2 * Module.finrank (ZMod 2) (fixedSpace d.half K) ≤
        rank (⊤ : Subgroup A) + 2 * Module.finrank (ZMod 2) (fixedSpace d.half ⊤) := by
    have hm := maximum_fixed_weight_comparison_all S U A (K.map A.subtype) hUS hA
      (map_subtype_le K)
    have ht := hfixed ⊤
    rw [htop] at ht
    have hr := rank_map_injective A.subtype A.subtype_injective (⊤ : Subgroup A)
    rw [htop] at hr
    rw [hfixed K, ht, rank_map_injective A.subtype A.subtype_injective, hr]
      at hm
    exact hm
  have himage : (⊤ : Subgroup A).map ((QuotientGroup.mk' Q).comp A.subtype) =
      A.map (QuotientGroup.mk' Q) := by rw [← map_map, htop]
  refine ⟨⟨hne, IsElementaryAbelian.map _⟩, ?_⟩
  intro B hBA
  let : IsElementaryAbelian 2 (⊤ : Subgroup A) := by
    exact {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
        Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) (x : A))) }
  have hb := central_line_quotient_weight_comparison d.half σ
    ((QuotientGroup.mk' Q).comp A.subtype) d.projection d.surjective ⊤
    (fun a _ v => d.quotient_action a v) (fun v hv a => d.central hv a)
    d.line hdouble B (himage.symm ▸ hBA)
  rwa [himage] at hb


/-- Intrinsic generation of the actual Thompson image, once each maximum
member has a doubled central lift. Source construction of those lifts is a
separate obligation; the quotient-only `PairedSection` does not provide it. -/
theorem thompson_image_generated_of_doubledCentralLifts
    (C U Q : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] [Q.Normal]
    (hUC : U ≤ C) (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G))
    (σ : Representation (ZMod 2) (G ⧸ Q) W)
    (hlift : ∀ A ∈ Stellmacher.elementaryAbelianMaxSubgroups C,
      A.map (QuotientGroup.mk' Q) ≠ ⊥ →
      Nonempty (DoubledCentralLift (V := V) U A Q f hf hker σ)) :
    offenderSubgroup
      (σ.comp ((Stellmacher.elementaryAbelianMaxJ C).map (QuotientGroup.mk' Q)).subtype) = ⊤ := by
  apply thompson_image_generated_of_maximum_images_best
  intro A hA hne
  obtain ⟨d⟩ := hlift A hA hne
  exact maximum_image_best_of_doubledCentralLift C U A Q hUC hA f hf hker σ d hne

omit [Finite G] in
/-- The source maximum-family comparison places the literal image of J(S)
inside the same Thompson actor I. A Sylow subgroup of I contains that image.
This does not identify a Thompson subgroup with an intersection. -/
theorem sylow_contains_marked_thompson_image
    (C S Q : Subgroup G) [Q.Normal] (hS : IsPGroup 2 S)
    (hcompare : ∀ A ∈ Stellmacher.elementaryAbelianMaxSubgroups S,
      A ∈ Stellmacher.elementaryAbelianMaxSubgroups C) :
    let q := QuotientGroup.mk' Q
    let I := (Stellmacher.elementaryAbelianMaxJ C).map q
    let J := (Stellmacher.elementaryAbelianMaxJ S).map q
    J ≤ I ∧ J.subgroupOf I ≤ (S.map q).subgroupOf I ∧
      ∃ P : Sylow 2 I, J.subgroupOf I ≤ (P : Subgroup I) := by
  dsimp only
  have hJC : Stellmacher.elementaryAbelianMaxJ S ≤ Stellmacher.elementaryAbelianMaxJ C :=
    sSup_le (fun A hA => le_sSup (hcompare A hA))
  have hJS : Stellmacher.elementaryAbelianMaxJ S ≤ S :=
    sSup_le (fun _ hA => hA.1)
  refine ⟨map_mono hJC, fun x hx => map_mono hJS hx, ?_⟩
  exact ((hS.to_le hJS).map (QuotientGroup.mk' Q)).comap_subtype.exists_le_sylow

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction
