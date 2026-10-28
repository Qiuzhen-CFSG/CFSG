module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.Actor
public import Theory.Representation.SLThreeCentralExtension.Stabilizers
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.GroupTheory.SelfNormalizingSylow

/-!
# The actual point stabilizer of a positive natural cover

Every common normalizer of L and its original moved subgroup acts through
L/O₂(L). The positive cover has sixteen vectors and a fourteen-vector orbit
outside its central line. A nonfixed vector consequently has stabilizer A₄.
If the common normalizer has a self-normalizing Sylow two-subgroup, Frattini
puts its entire image in the Klein four. No element of order three from L
can lie there, because its kernel on the cover is a two-group.

Models.PositiveExclusion supplies this common normalizer, its Sylow subgroup
and the opposite cubic from the original constrained context.
Source: Aschbacher--Smith B.4.8 and10.2.9, printed pp.91 and752.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02
open scoped IsMulCommutative MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- A positive natural cover admits no nontrivial cubic from its component
inside a Sylow-self-normalizing common normalizer fixing a nonkernel vector. -/
theorem no_positive_cover_stabilizer_cubic
    (hmodel : Selection.BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (H : Subgroup G) (hHL : H ≤ normalizer (L : Set G))
    (hHW : H ≤ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (S : Sylow 2 H) (hS : normalizer (S : Set H) = S)
    {w : G} (hw : w ∈ ⁅D.fullModule,L⁆) (hwn : w ∉ centralizer (L : Set G))
    (hHfix : H ≤ centralizer ({w} : Set G))
    {y : G} (hyH : y ∈ H) (hyL : y ∈ L) (hy3 : orderOf y = 3) : False := by
  let W := ⁅D.fullModule,L⁆
  let : IsElementaryAbelian 2 W := source_original_full_moved_elementary D
  obtain ⟨e,σ,p,hp,hσ,hker⟩ := Selection.BinaryThree.moved_cover D hmodel
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  change ∀ (l : L) (x : Additive W), ((σ (q l) x).toMul : G) =
    l*x.toMul*(l : G)⁻¹ at hσ
  let τ := BinaryConjugationSection.originalNormalizerAction hHW
  have hex (a : H) : ∃ g, σ g = τ a := by
    obtain ⟨l,hl,hact⟩ := Selection.BinaryThree.common_normalizer_acts_through_component
      D hmodel (hHL a.property) (hHW a.property)
    refine ⟨q ⟨l,hl⟩,?_⟩
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hσ,BinaryConjugationSection.originalNormalizerAction_apply_coe]
    exact (hact x.toMul x.toMul.property).symm
  have hσinj := OneCohomology.SLThreeCentralExtension.cover_faithful σ p hp
  choose θ hθ using hex
  let π : H →* BinaryLinearThree.Group := {
    toFun := θ
    map_one' := hσinj (by rw [hθ,map_one,map_one])
    map_mul' a b := hσinj (by simp only [map_mul,hθ]) }
  have hπact (a : H) : σ (π a) = τ a := hθ a
  let x : Additive W := Additive.ofMul ⟨w,hw⟩
  have hx : p x ≠ 0 := fun h => hwn ((hker x).mp h).2
  have hpk : p.toLinearMap.ker ≠ ⊥ := by
    intro hz
    apply hne
    apply bot_unique
    intro z hzK
    have hh : (Additive.ofMul ⟨z,hzK.1⟩ : Additive W) ∈ p.toLinearMap.ker :=
      (hker _).mpr hzK
    rw [hz] at hh
    exact mem_bot.mpr (congrArg (fun a : Additive W => (a.toMul : G)) hh)
  let St := OneCohomology.SLThreeCentralExtension.vectorStabilizer σ x
  have hStnat : St ≤ BinaryLinearThree.OrbitStabilizers.natural (p x) := by
    intro g hg
    rw [BinaryLinearThree.OrbitStabilizers.mem_natural,←p.isIntertwining]
    exact congrArg p hg
  have hStcard : Nat.card St = 12 := by
    have hcW : Nat.card (Additive W) = 16 :=
      Selection.BinaryThree.moved_card_eq_sixteen D hmodel hne
    have hcK : Nat.card p.toLinearMap.ker = 2 := by
      let f : p.toLinearMap.ker ≃ sourceMovedFixed D := {
        toFun := fun z => ⟨z.val.toMul,(hker z.val).mp z.property⟩
        invFun := fun z => ⟨Additive.ofMul ⟨z.val,z.property.1⟩,(hker _).mpr z.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      exact (Nat.card_congr f).trans (Selection.BinaryThree.moved_fixed_card_eq_two D hmodel hne)
    have hr : Set.range (fun g => σ g x) = (p.toLinearMap.ker : Set (Additive W))ᶜ := by
      ext z
      constructor
      · rintro ⟨g,rfl⟩ hz
        have hh : p (σ g x) = 0 := hz
        rw [p.isIntertwining] at hh
        exact hx ((BinaryLinearThree.W.apply_bijective g).1
          (hh.trans (map_zero _).symm))
      · intro hz
        exact OneCohomology.SLThreeCentralExtension.transitive_outside_kernel_of_cover
          p hp hpk x z hx hz
    have hi : St.index = 14 := by
      rw [OneCohomology.SLThreeCentralExtension.vectorStabilizer_index,hr]
      change ((p.toLinearMap.ker : Set (Additive W))ᶜ).ncard = 14
      rw [Set.ncard_compl]
      change Nat.card (Additive W) - Nat.card p.toLinearMap.ker = 14
      rw [hcW,hcK]
    have hh := St.card_mul_index
    rw [hi,Matrix.PSL3Two.card_SL] at hh
    omega
  let E := BinaryLinearThree.OrbitStabilizers.twelveEquivAlternating St (p x) hx hStnat hStcard
  let f : H →* alternatingGroup (Fin 4) := E.toMonoidHom.comp
    (π.codRestrict St (fun a => by
      change σ (π a) x = x
      rw [hπact]
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [BinaryConjugationSection.originalNormalizerAction_apply_coe]
      change (a : G)*w*(a : G)⁻¹ = w
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hHfix a.property))))
  have hf := S.image_le_kleinFour_of_self_normalizing hS f
  let yH : H := ⟨y,hyH⟩
  have hπy : π yH = q ⟨y,hyL⟩ := by
    apply hσinj
    rw [hπact]
    apply LinearMap.ext
    intro z
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hσ,BinaryConjugationSection.originalNormalizerAction_apply_coe]
  have hfy : f yH ≠ 1 := by
    intro hz
    have hπone : π yH = 1 := congrArg Subtype.val (E.map_eq_one_iff.mp hz)
    rw [hπy] at hπone
    have hcore : (⟨y,hyL⟩ : L) ∈ pCore 2 L :=
      (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp hπone)
    let z : pCore 2 L := ⟨⟨y,hyL⟩,hcore⟩
    have hz3 : orderOf z = 3 := (Subgroup.orderOf_coe z).symm.trans
      ((Subgroup.orderOf_coe (⟨y,hyL⟩ : L)).symm.trans hy3)
    have hz0 : z ≠ 1 := by intro h; rw [h,orderOf_one] at hz3; omega
    have htwo := (pCore_isPGroup (p := 2) (G := L)).dvd_orderOf hz0
    rw [hz3] at htwo
    norm_num at htwo
  let z : alternatingGroup.kleinFour (Fin 4) := ⟨f yH,hf ⟨yH,rfl⟩⟩
  have hz3 : orderOf z = 3 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change (f yH)^3 = 1
      rw [←map_pow]
      have hy : yH^3 = 1 := Subtype.ext (hy3 ▸ pow_orderOf_eq_one y)
      rw [hy,map_one]
    · exact fun h => hfy (congrArg Subtype.val h)
  have hdiv := orderOf_dvd_natCard z
  rw [hz3,alternatingGroup.kleinFour_card_of_card_eq_four (by simp)] at hdiv
  norm_num at hdiv
end CFSG.Quasithin.Chapter10.PointControl.Constrained
