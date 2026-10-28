module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max1Reducibility
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalOvergroups.TrioPlacement
import all CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max1Reducibility
import all CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility
/-!
# Compatible actors in the actual J₄ local groups

The max1 and max2 pair calculations use their literal quotient maps and
compatible Sylow actions. They do not use maximality of the overgroup.
These versions retain exactly those hypotheses, so they apply to overgroups
obtained from the source pair's elementary normal closure.

This is an intentional internal proof split: `import all` reuses the private
Mathieu pair-input and quotient-reducibility lemmas from the existing adequate
reduction. Those helpers do not appear in the public statements; the original
maximal-overgroup interfaces remain unchanged.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511. All actual matrix
quotient, pair incidence and Mathieu alternative inputs are discharged here.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate
open MathieuAbsorption Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] Janko4.modelGroup
set_option backward.isDefEq.respectTransparency true

/-- Compatible actors in a max1-type overgroup preserve a proper Frattini subgroup. -/
theorem max1_actorReducible_of_compatible
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (R : Subgroup Janko4.Model) (h : PairInput S R)
    (M : Subgroup Janko4.Model) (hSM : S.toSubgroup ≤ M) (hRM : R ≤ M)
    (e : M ≃* Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (D : Subgroup (MulAut R)) (htwo : IsPGroup 2 D)
    (hactions : CompatibleSylowActions S.toSubgroup R M hRM D) : ActorReducible D := by
  have htrio := M24PairAction.reducibleOrTrioPlacement
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : M →* M24 := projection.comp e.toMonoidHom
  have hf : Function.Surjective f := projection_surjective.comp e.surjective
  have hk : IsPGroup 2 f.ker :=
    projection_ker_isPGroup.comap_of_injective e.toMonoidHom e.injective
  have hi : Function.Injective (f.comp (R.subgroupOf M).subtype) := by
    apply injective_comp_subtype_of_coprime_ker f _ _ h.oddComplement.isPGroup.comap_subtype
    obtain ⟨n, hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let U := (R.subgroupOf M).map f
  let eR : R ≃* U := (subgroupOfEquivOfLe hRM).symm.trans
    (MulEquiv.ofBijective (f.subgroupMap (R.subgroupOf M))
      ⟨fun _ _ he => hi (congrArg Subtype.val he), f.subgroupMap_surjective _⟩)
  have heR (r : R) : (eR r : M24) = f (inclusion hRM r) := rfl
  let T := (S.subtype hSM).mapSurjective hf
  have hp : PairInput T U := quotient_pair_input h M hSM hRM f hf hk eR
  have hred := mathieu_pair_reducible htrio T U hp
  let a := MulAut.congr eR
  let D' := D.map a.toMonoidHom
  have hD' : D' ≤ pairAutomizer T.toSubgroup U := by
    rintro b ⟨b, hb, rfl⟩
    obtain ⟨c, hcS, hcR⟩ := hactions b hb
    obtain ⟨d, hd⟩ := exists_quotientActor (MulAut.congr e c)
    have hfd (x : M) : f (c x) = d (f x) := by
      change projection (e (c x)) = d (projection (e x))
      have hh := hd (e x)
      simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using hh
    refine ⟨d, ?_, ?_⟩
    · intro y
      constructor
      · rintro ⟨x, hx, he⟩
        refine ⟨c.symm x, ?_, ?_⟩
        · exact (hcS (c.symm x)).mp (by rwa [c.apply_symm_apply])
        · apply d.injective
          rw [← hfd, c.apply_symm_apply, he]
      · rintro ⟨x, hx, rfl⟩
        exact ⟨c x, (hcS x).mpr hx, hfd x⟩
    · intro y
      obtain ⟨r, rfl⟩ := eR.surjective y
      change (MulAut.congr eR b (eR r) : M24) = d (eR r)
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [heR, heR, hcR, hfd]
  obtain ⟨A, hAb, hAt, hA⟩ := hred D' hD' (htwo.map a.toMonoidHom)
  let q := frattiniEquiv eR
  refine ⟨A.comap q.toMonoidHom, ?_, ?_, ?_⟩
  · intro hb
    apply hAb
    have hh := congrArg (Subgroup.map q.toMonoidHom) hb
    rwa [map_comap_eq_self_of_surjective (f := q.toMonoidHom) q.surjective A,
      Subgroup.map_bot] at hh
  · intro ht
    apply hAt
    have hh := congrArg (Subgroup.map q.toMonoidHom) ht
    rwa [map_comap_eq_self_of_surjective (f := q.toMonoidHom) q.surjective A,
      map_top_of_surjective q.toMonoidHom q.surjective] at hh
  · intro b hb x hx
    change q (quotientAut (frattini R) b x) ∈ A
    rw [frattiniEquiv_equivariant]
    exact hA (a b) ⟨b, hb, rfl⟩ (q x) hx


/-- Compatible actors in a max2-type overgroup preserve a proper Frattini subgroup. -/
theorem max2_actorReducible_of_compatible
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (R : Subgroup Janko4.Model) (h : PairInput S R)
    (M : Subgroup Janko4.Model) (hSM : S.toSubgroup ≤ M) (hRM : R ≤ M)
    (e : M ≃* sourceSubgroup) (D : Subgroup (MulAut R))
    (hact : CompatibleSylowActions S.toSubgroup R M hRM D) : ActorReducible D := by
  have hC := Max2.matrix_threeCore_card
  have hcontains := Max2.elementaryCubicContainment_of_threeCore_card hC
  have hexclude := Max2.order27Exclusion
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : IsPGroup 3 R := h.oddComplement.isPGroup
  let f := (Max2.projection e).comp (inclusion hRM)
  let T := Max2.quotientSylow S hSM e
  have hi : Function.Injective f := Max2.complement_injective e hRM h3
  have hp : (f.range : Set Max2.MatrixGroup) * (T : Set Max2.MatrixGroup) =
      (T : Set Max2.MatrixGroup) * (f.range : Set Max2.MatrixGroup) :=
    Max2.pair_permutes S hSM hRM e h.permutes
  have hc : Nat.card f.range = Nat.card R := Max2.complement_card e hRM h3
  rcases h.oddComplement with ⟨hE, hcard⟩ | ⟨_hEx, hcard, _hexp⟩
  · let _ := hE
    have hE' : IsElementaryAbelian 3 f.range := Max2.complement_elementary e hRM hE
    have hline : pCore 3 Max2.MatrixGroup ≤ f.range :=
      hcontains T f.range hE' (hc.trans hcard) hp
    exact actorReducible_of_characteristic_cubic hcard D f hi
      (pCore 3 Max2.MatrixGroup) hC hline (Max2.compatible_quotientActors e hRM D hact)
  · exact (Max2.not_order27_pair hexclude T f.range
      (h3.of_surjective f.rangeRestrict f.rangeRestrict_surjective) (hc.trans hcard) hp).elim

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate
