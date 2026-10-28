module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TrappedCommutator

/-!
# Nontrapping of the full starting radius

The scalar isotropic-plane comparison underlying
`SymplecticFourOrthogonalCover.HyperplaneMovement` also gives containment of
the hyperplane commutator in the original root preimage. The local proof below
retains that containment. The full root geometry identifies this preimage
inside the literal critical-root commutator, including the entire central
covering kernel.

For the original trapped configuration, the terminal residual twist preserves
the same source commutator and identifies it with the whole-U commutator of
the inverse-transformed seed. Its containment in the original critical-root
commutator reverses full fixed-kernel containment by symplectic duality.
The transformed seed therefore fixes the original endpoint intersection,
forcing the same nonzero source commutator to be trivial.

The concluding application excludes trapping of the full starting radius,
with no additional intersection, action or fixed-layer hypothesis. The source
selector compatibility, terminal distance exclusions and minimum-replacement
assembly remain separate steps toward the distance-two witness.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two,
MS93 (3.3)(ii) and (5.8), printed pp.867,920. The local scalar comparison
retains the proof of `HyperplaneMovement` with its stronger output for this
particular source consumer; shared foundational modules remain unchanged.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour.TwoLocalCover
open Representation.SymplecticFourOrthogonalCover
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.TrappedRootComparison
section Linear
variable {F : Type*} [Field F]
private noncomputable def hyperplaneDisplacement (Y : Subgroup (Sp F))
    (A : Submodule F (Vector F)) : Submodule F (Vector F) :=
  ⨆ y : Y, A.map (symplecticNatural 2 y.val - LinearMap.id)

private theorem hyperplaneDisplacement_le (Y : Subgroup (Sp F)) (A : Submodule F (Vector F)) :
    hyperplaneDisplacement Y A ≤ displacementSpace Y := by
  apply iSup_le
  intro y v hv
  obtain ⟨w,hw,rfl⟩ := hv
  exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp Y.subtype) y w

private theorem hyperplane_displacement_le_root
    (Y : Subgroup (Sp F)) (R : Submodule F (Vector F))
    (hd : Module.finrank F R = 1)
    (hfix : ∀ y ∈ Y, ∀ v ∈ R, y • v = v)
    (hq : ∀ x ∈ Y, ∀ y ∈ Y, ∀ v ∈ (form F).orthogonal R,
      x • (y • v-v)=y • v-v)
    (hbad : ¬ displacementSpace Y ≤ R ⊔ hyperplaneDisplacement Y ((form F).orthogonal R)) :
    hyperplaneDisplacement Y ((form F).orthogonal R) ≤ R := by
  let A := (form F).orthogonal R
  let W := hyperplaneDisplacement Y A
  let B := R ⊔ W
  have hWP : W ≤ displacementSpace Y := hyperplaneDisplacement_le Y A
  have hRf : R ≤ fixedSpace Y := fun v hv y hy => hfix y hy v hv
  have hWf : W ≤ fixedSpace Y := by
    apply iSup_le
    intro y w hw
    obtain ⟨v,hv,rfl⟩ := hw
    exact fun x hx => hq x hx y.val y.property v hv
  have hBf : B ≤ fixedSpace Y := sup_le hRf hWf
  have hiso : ∀ v ∈ B, ∀ w ∈ B, form F v w = 0 := by
    have hRR : R ≤ (form F).orthogonal R := by
      have hne : R ≠ ⊥ := by intro h; rw [h,finrank_bot] at hd; omega
      obtain ⟨v,hv,hv0⟩ := R.ne_bot_iff.mp hne
      have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hd hv hv0
      intro x hx y hy
      rw [hspan] at hx hy
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨d,rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [form_alternating v]
    have hRW : R ≤ (form F).orthogonal W := by
      intro r hr w hw
      exact (orthogonal_displacementSpace Y ▸ hRf hr) w (hWP hw)
    have hWW : W ≤ (form F).orthogonal W := by
      intro v hv w hw
      exact (orthogonal_displacementSpace Y ▸ hWf hv) w (hWP hw)
    intro v hv w hw
    obtain ⟨r,hr,s,hs,rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨t,ht,u,hu,rfl⟩ := Submodule.mem_sup.mp hw
    simp only [map_add,LinearMap.add_apply,hRR ht r hr,form_alternating.eq_iff.mp (hRW hr u hu),
      hRW ht s hs,hWW hu s hs,add_zero]
  have hBdim := finrank_le_two_of_isotropic B hiso
  have hless : Module.finrank F B < 2 := by
    by_contra! h
    have he : Module.finrank F B = 2 := by omega
    have hBo : (form F).orthogonal B = B := by
      symm
      apply Submodule.eq_of_le_of_finrank_eq
      · exact fun v hv w hw => hiso w hw v hv
      · rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,he]
        simp [Theory.SpecificGroups.SymplecticFour.Vector]
    apply hbad
    intro v hv
    change v ∈ B
    rw [←hBo]
    intro w hw
    exact form_alternating.eq_iff.mp ((orthogonal_displacementSpace Y ▸ hBf hw) v hv)
  have hle : Module.finrank F B ≤ Module.finrank F R := by omega
  have heq : R = B := Submodule.eq_of_le_of_finrank_le le_sup_left hle
  exact (le_sup_right : W ≤ B).trans heq.ge

end Linear
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := F)) W}
omit [Finite F] [CharP F 2] [FiniteDimensional (ZMod 2) W] in
private theorem embedded_standard_hyperplane_le_root
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y A N : Subgroup G) (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hA : ∀ w : W, j (Multiplicative.ofAdd w) ∈ A ↔ p w ∈ (form F).orthogonal (point F))
    (hAr : A ≤ j.range)
    (hroot : ∀ w : W, p w ∈ point F → j (Multiplicative.ofAdd w) ∈ N)
    (hfix : ∀ y : Y, ∀ v ∈ point F, (β y).val • v=v)
    (hquad : ⁅⁅A,Y⁆,Y⁆ = ⊥)
    (hAN : ⁅Y,A⁆ ≤ N) (hbad : ¬ ⁅Y,j.range⁆ ≤ N) :
    ⁅Y,A⁆ ≤ (((point F).restrictScalars (ZMod 2)).comap p.toLinearMap).toAddSubgroup.toSubgroup.map j := by
  let α : Y →* Sp F := (commutator (Sp F)).subtype.comp β
  let H := (form F).orthogonal (point F)
  let D := hyperplaneDisplacement α.range H
  have hdisp (y : Y) (w : W) :
      j (Multiplicative.ofAdd (σ (β y) w-w))=⁅y.val,j (Multiplicative.ofAdd w)⁆ := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
    rfl
  have hD : ∀ v ∈ D, ∃ w : W, p w=v ∧ j (Multiplicative.ofAdd w) ∈ N := by
    intro v hv
    refine Submodule.iSup_induction _
      (motive := fun v => ∃ w : W, p w=v ∧ j (Multiplicative.ofAdd w) ∈ N) hv ?_ ?_ ?_
    · intro y u hu
      obtain ⟨y,hy⟩ := y.property
      rw [←hy] at hu
      obtain ⟨v,hv,rfl⟩ := hu
      obtain ⟨w,rfl⟩ := hp.1 v
      refine ⟨σ (β y) w-w,by rw [map_sub,p.isIntertwining]; rfl,?_⟩
      rw [hdisp]
      exact hAN
        (commutator_mem_commutator y.property ((hA w).mpr hv))
    · exact ⟨0,map_zero _,by simp⟩
    · rintro v u ⟨w,hw,hy⟩ ⟨w',hw',hy'⟩
      exact ⟨w+w',by rw [map_add,hw,hw'],by simpa only [ofAdd_add,map_mul] using N.mul_mem hy hy'⟩
  have hnot : ¬ displacementSpace α.range ≤ point F ⊔ D := by
    intro hd
    apply hbad
    apply commutator_le.mpr
    intro y hy u hu
    obtain ⟨w,rfl⟩ := hu
    let v := σ (β ⟨y,hy⟩) w.toAdd-w.toAdd
    have hv : p v ∈ displacementSpace α.range := by
      rw [show p v=α ⟨y,hy⟩ • p w.toAdd-p w.toAdd by rw [map_sub,p.isIntertwining]; rfl]
      exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp α.range.subtype)
        ⟨α ⟨y,hy⟩,⟨_,rfl⟩⟩ _
    obtain ⟨r,hr,s,hs,he⟩ := Submodule.mem_sup.mp (hd hv)
    obtain ⟨wr,hwr⟩ := hp.1 r
    obtain ⟨ws,hws,hsY⟩ := hD s hs
    have hk : p (v-wr-ws)=0 := by rw [map_sub,map_sub,hwr,hws,←he]; abel
    have hh := N.mul_mem (N.mul_mem (hroot wr (hwr ▸ hr)) hsY)
      (hroot (v-wr-ws) (hk ▸ Submodule.zero_mem _))
    rw [←map_mul,←map_mul,←ofAdd_add,←ofAdd_add] at hh
    have hv' : wr+ws+(v-wr-ws)=v := by abel
    rw [hv',hdisp] at hh
    exact hh
  have hq : ∀ x ∈ α.range, ∀ y ∈ α.range, ∀ v ∈ H,
      x • (y • v-v)=y • v-v := by
    rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩ v hv
    obtain ⟨w,rfl⟩ := hp.1 v
    have hm : j (Multiplicative.ofAdd (σ (β y) w-w)) ∈ ⁅A,Y⁆ := by
      rw [hdisp,commutator_comm A Y]
      exact commutator_mem_commutator y.property ((hA w).mpr hv)
    have he : σ (β x) (σ (β y) w-w)=σ (β y) w-w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact,(commutator_eq_bot_iff_le_centralizer.mp hquad) hm x.val x.property,
        mul_inv_cancel_right]
    have he' := congrArg p he
    rw [p.isIntertwining,map_sub,p.isIntertwining] at he'
    exact he'
  have hle : D ≤ point F := hyperplane_displacement_le_root α.range (point F) finrank_point
    (by rintro y ⟨y,rfl⟩ v hv; exact hfix y v hv) hq hnot
  apply commutator_le.mpr
  intro y hy a ha
  obtain ⟨w,hw⟩ := hAr ha
  have hwA : p w.toAdd ∈ H := (hA w.toAdd).mp (hw ▸ ha)
  refine ⟨Multiplicative.ofAdd (σ (β ⟨y,hy⟩) w.toAdd-w.toAdd),?_,?_⟩
  · change p (σ (β ⟨y,hy⟩) w.toAdd-w.toAdd) ∈ point F
    rw [map_sub,p.isIntertwining]
    apply hle
    exact (le_iSup (fun y : α.range => H.map (symplecticNatural 2 y.val-LinearMap.id))
      ⟨α ⟨y,hy⟩,⟨_,rfl⟩⟩) ⟨p w.toAdd,hwA,rfl⟩
  · rw [hdisp]
    exact congrArg (fun r => ⁅y,r⁆) hw

private theorem standard_root_commutator_preimage
    (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (Y T : Subgroup G) (hTY : T ≤ Y)
    (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hT : ((β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)=RootSubgroup.group 0)
    (w : W) (hw : p w ∈ point F) : j (Multiplicative.ofAdd w) ∈ ⁅T,j.range⁆ := by
  have hw' : w ∈ Coinvariants.ker (σ.comp Roots.group.subtype) :=
    (Roots.cover_root_geometry hF p hp).2.1 ▸ hw
  clear hw
  induction hw' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨a,v⟩,rfl⟩ := hw
    obtain ⟨_,⟨t,rfl⟩,ht⟩ := (show a.val.val ∈
        (β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype from hT.symm ▸ a.property)
    have he : β (inclusion hTY t)=a.val := Subtype.ext ht
    change j (Multiplicative.ofAdd (σ a.val v-v)) ∈ ⁅T,j.range⁆
    rw [ofAdd_sub,map_div,div_eq_mul_inv,←he,hact]
    exact commutator_mem_commutator t.property (show j (Multiplicative.ofAdd v) ∈ j.range from ⟨_,rfl⟩)
  | zero => simp only [ofAdd_zero,map_one,one_mem]
  | add x y _ _ hx hy =>
    rw [ofAdd_add,map_mul]
    exact (⁅T,j.range⁆).mul_mem hx hy
  | smul c v _ hv =>
    fin_cases c
    · change j (Multiplicative.ofAdd ((0 : ZMod 2) • v)) ∈ ⁅T,j.range⁆
      simp only [zero_smul,ofAdd_zero,map_one,one_mem]
    · change j (Multiplicative.ofAdd ((1 : ZMod 2) • v)) ∈ ⁅T,j.range⁆
      simpa only [one_smul] using hv

private theorem standard_root_fixed_iff
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y T : Subgroup G) (hTY : T ≤ Y) (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hT : ((β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)=RootSubgroup.group 0)
    (w : W) : j (Multiplicative.ofAdd w) ∈ centralizer (T : Set G) ↔
      p w ∈ (form F).orthogonal (point F) := by
  rw [←PointRadicalAction.root_displacement,orthogonal_displacementSpace]
  constructor
  · intro hw a ha
    obtain ⟨_,⟨t,rfl⟩,ht⟩ := hT.symm ▸ ha
    have he : σ (β (inclusion hTY t)) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact]
      change t.val*j (Multiplicative.ofAdd w)*t.val⁻¹=_
      rw [hw t.val t.property,mul_inv_cancel_right]
    have he' := congrArg p he
    rw [p.isIntertwining] at he'
    exact ht ▸ he'
  · intro hw t ht
    have hmem : (β (inclusion hTY ⟨t,ht⟩)).val ∈ RootSubgroup.group 0 :=
      hT ▸ mem_map_of_mem _ (show β (inclusion hTY ⟨t,ht⟩) ∈
        (β.comp (inclusion hTY)).range from ⟨_,rfl⟩)
    have he := congrArg (fun w => j (Multiplicative.ofAdd w))
      (cover_fixed_of_projection_fixed p hp (β (inclusion hTY ⟨t,ht⟩)) w (hw _ hmem))
    rw [hact,mul_inv_eq_iff_eq_mul] at he
    exact he

/-- The full-cover hyperplane comparison retains containment in the literal
root commutator. This interface is also used for the consecutive critical
kernels in the terminal normalizer comparison, MS93 (5.10). -/
theorem embedded_root_hyperplane_le_commutator_of_comparison
    (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y T : Subgroup G) (hTY : T ≤ Y) (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hcard : Nat.card (β.comp (inclusion hTY)).range = Nat.card F)
    (hd : Module.finrank F (displacementSpace
      ((β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)) = 1)
    (hrootquad : ∀ x ∈ (β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype,
      ∀ y ∈ (β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hcomm : ⁅T,j.range⁆ ≤ T) (hcent : Y ≤ centralizer (T : Set G))
    (hquad : ⁅⁅j.range ⊓ centralizer (T : Set G),Y⁆,Y⁆ = ⊥)
    (hbad : ¬ ⁅Y,j.range⁆ ≤ T ⊔ ⁅Y,j.range ⊓ centralizer (T : Set G)⁆) :
    ⁅Y,j.range ⊓ centralizer (T : Set G)⁆ ≤ ⁅T,j.range⁆ := by
  have hcard' : Nat.card ((β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)=Nat.card F := by
    rw [card_map_of_injective (commutator (Sp F)).subtype_injective,hcard]
  obtain ⟨g,hg⟩ := FourLongRoots.exists_conjugate_root_of_displacement_one _ hcard' hd hrootquad
  let gl : L (K := F) := ⟨g,by rw [Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF]; trivial⟩
  let β' := (MulAut.conj gl).toMonoidHom.comp β
  let j' := j.comp (σ gl⁻¹).toAddMonoidHom.toMultiplicative
  have hj' : Function.Injective j' := hj.comp
    (fun x y he => Multiplicative.toAdd.injective ((σ.apply_bijective gl⁻¹).1 (congrArg Multiplicative.toAdd he)))
  have hjr : j'.range=j.range := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top_of_surjective _
      (show Function.Surjective (σ gl⁻¹).toAddMonoidHom.toMultiplicative from fun w => by
        obtain ⟨v,hv⟩ := (σ.apply_bijective gl⁻¹).2 w.toAdd
        exact ⟨Multiplicative.ofAdd v,congrArg Multiplicative.ofAdd hv⟩),←MonoidHom.range_eq_map]
  have hact' (y : Y) (w : W) : j' (Multiplicative.ofAdd (σ (β' y) w)) =
      y.val*j' (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (σ gl⁻¹ (σ (gl*β y*gl⁻¹) w)))=_
    simp only [map_mul,Module.End.mul_apply,inv_self_apply]
    exact hact y (σ gl⁻¹ w)
  have hT' : ((β'.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)=RootSubgroup.group 0 := by
    rw [←hg]
    ext x
    constructor
    · rintro ⟨_,⟨t,rfl⟩,rfl⟩
      exact ⟨(β (inclusion hTY t)).val,mem_map_of_mem _ ⟨t,rfl⟩,rfl⟩
    · rintro ⟨_,⟨_,⟨t,rfl⟩,rfl⟩,rfl⟩
      exact ⟨β' (inclusion hTY t),⟨t,rfl⟩,rfl⟩
  have hroot (w : W) (hw : p w ∈ point F) : j' (Multiplicative.ofAdd w) ∈ T := by
    rw [←hjr] at hcomm
    exact hcomm (standard_root_commutator_preimage hF p hp j' Y T hTY β' hact' hT' w hw)
  have hfix (y : Y) (v : Vector F) (hv : v ∈ point F) : (β' y).val • v=v := by
    obtain ⟨w,rfl⟩ := hp.1 v
    have he : σ (β' y) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj'
      rw [hact',←hcent y.property _ (hroot w hv),mul_inv_cancel_right]
    exact (LinearMap.congr_fun (p.isIntertwining' (β' y)) w).symm.trans (congrArg p he)
  have bound := embedded_standard_hyperplane_le_root p hp j' hj'
    Y (j'.range ⊓ centralizer (T : Set G))
    (T ⊔ ⁅Y,j'.range ⊓ centralizer (T : Set G)⁆) β' hact'
    (fun w => by
      rw [mem_inf,standard_root_fixed_iff p hp j' hj' Y T hTY β' hact' hT']
      exact and_iff_right ⟨_,rfl⟩)
    inf_le_left (fun w hw => mem_sup_left (hroot w hw)) hfix
    (by rwa [hjr]) le_sup_right (by rwa [hjr])
  rw [←hjr]
  refine bound.trans ?_
  rintro _ ⟨w,hw,rfl⟩
  exact standard_root_commutator_preimage hF p hp j' Y T hTY β' hact' hT' w.toAdd hw

private theorem embedded_root_hyperplane_le_commutator
    (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y T : Subgroup G) (hTY : T ≤ Y) (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hcard : Nat.card (β.comp (inclusion hTY)).range = Nat.card F)
    (hd : Module.finrank F (displacementSpace
      ((β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)) = 1)
    (hrootquad : ∀ x ∈ (β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype,
      ∀ y ∈ (β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hcomm : ⁅T,j.range⁆ ≤ T) (hcent : Y ≤ centralizer (T : Set G))
    (hquad : ⁅⁅j.range ⊓ centralizer (T : Set G),Y⁆,Y⁆ = ⊥)
    (hn : j.range ⊓ centralizer (T : Set G) ≤ normalizer (Y : Set G))
    (hbad : ¬ j.range ≤ normalizer (Y : Set G)) :
    ⁅Y,j.range ⊓ centralizer (T : Set G)⁆ ≤ ⁅T,j.range⁆ := by
  apply embedded_root_hyperplane_le_commutator_of_comparison hF p hp j hj Y T hTY β hact
    hcard hd hrootquad hcomm hcent hquad
  intro hc
  apply hbad
  exact le_normalizer_iff_commutator_le_left.mpr (hc.trans
    (sup_le hTY (le_normalizer_iff_commutator_le_left.mp hn)))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.TrappedRootComparison

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open scoped Pointwise
private theorem commutator_fixed_supplement_bound
    {G : Type*} [Group G] (X U D Y T : Subgroup G)
    (hX : X=U ⊔ D) (hDU : D ≤ normalizer (U : Set G))
    (hDY : D ≤ centralizer (Y : Set G)) (hTY : T ≤ Y) :
    ⁅Y,X ⊓ centralizer (T : Set G)⁆ ≤ ⁅Y,U ⊓ centralizer (T : Set G)⁆ := by
  apply commutator_le.mpr
  intro y hy x hx
  have hx' : x ∈ (U : Set G)*(D : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left U D hDU,←hX]
    exact hx.1
  obtain ⟨u,hu,c,hc,rfl⟩ := hx'
  have huT : u ∈ centralizer (T : Set G) := by
    have hh := (centralizer (T : Set G)).mul_mem hx.2
      ((centralizer (T : Set G)).inv_mem ((centralizer_le hTY) (hDY hc)))
    simpa only [mul_inv_cancel_right] using hh
  have hcY : ⁅y,c⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hDY hc y hy)
  rw [commutatorElement_mul_right_eq_mul_conj,hcY,mul_one,mul_inv_cancel_right]
  exact commutator_mem_commutator hy ⟨hu,huT⟩

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The trapped source commutator lies in the original critical-root
commutator on the whole cover, with the same nonnormal neighboring seed. -/
theorem Input.replacement_trapped_root_commutator_le_critical
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    ⁅Z d.radical v,U d.radical z ⊓ Q d.radical a⁆ ≤ ⁅Z d.radical a,U d.radical z⁆ := by
  let Y := Z d.radical v ⊔ Z d.radical a
  let A := X d.radical z ⊓ Q d.radical a
  have hYV : Y ≤ V d.radical a := neighbor_seed_join_le_radius hat hvt
  have hYQ : Y ≤ Q d.radical a := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have haQ : Z d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
    apply Z_le_Q_of_dist_lt _ a (geometry.exists_critical a path.start_color)
    rw [path.dist_start (Nat.sub_le _ _),geometry.distance_constant a path.start_color]
    have hh := path.length_eq_b
    change path.walk.length-2 < geometry.b d.radical
    omega
  have hYtr : Y ≤ V d.radical a ⊓ Q d.radical (path.walk.getVert (path.walk.length-2)) :=
    le_inf hYV (sup_le htrap haQ)
  have hYS : Y ≤ stabilizer d.radical z := hYtr.trans
    (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hvS : Z d.radical v ≤ stabilizer d.radical z := le_sup_left.trans hYS
  obtain ⟨hi,hi'⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
    (by omega) (Z d.radical v) hvS (le_sup_left.trans hYQ) hn
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2 := by
    rw [hi]; nlinarith
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hUS : U d.radical z ≤ stabilizer d.radical a :=
    (U_le_Z z).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hAU : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ Q d.radical a := by
    rw [←hCa]
    ext x
    exact ⟨fun hx => ⟨hx.1,hUS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  have hZX : Z d.radical z ≤ X d.radical z := geometry.omega_bound z path.end_color
    (by rw [geometry.distance_constant z path.end_color]; exact lt_of_lt_of_le (by decide : 0 < 4) hb)
  have hUA : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) ≤ A := by
    rw [hAU]
    exact inf_le_inf ((U_le_Z z).trans hZX) le_rfl
  have hvcolor : color d.radical v=false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hvt
    rw [path.start_color] at h1
    cases ht : color d.radical t <;> cases hv : color d.radical v <;> simp_all
  have hAnv : A ≤ normalizer (Z d.radical v : Set (FreeAmalgam d.radical)) :=
    (inf_le_right.trans (Q_le_stabilizer_of_dist_le_two a v path.start_color hvcolor
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hat hvt))).trans
        (Z_normalized d.radical v)
  have hAna : A ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (inf_le_right.trans (fun _ hx => hx.1)).trans (Z_normalized d.radical a)
  have hAn : A ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp (hAnv hx),
      mem_normalizer_iff_map_conj_eq.mp (hAna hx)]
  have hquad : ⁅⁅A,Y⁆,Y⁆=⊥ := le_bot_iff.mp
    ((commutator_mono (commutator_mono le_rfl hYtr) hYtr).trans_eq
      (h.replacement_radius_commutator_bounds d geometry hb path.start_color z
        (path.walk.getVert (path.walk.length-2))).2)
  have hpos : 0 < geometry.b d.radical := by omega
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        a path.start_color (by rwa [geometry.distance_constant a path.start_color]) z path.end_color path.critical }
  let D := X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))
  have hsplit : X d.radical z=U d.radical z ⊔ D :=
    h.replacement_root_X_decomposition_center d rev hb hsmall
  have hDY : D ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hYS)
  have hbadU : ¬ U d.radical z ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    intro hh
    exact hn (hZX.trans (hsplit ▸ sup_le hh (hDY.trans (Subgroup.centralizer_le_normalizer _))))
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.end_color
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let β := (e.groupEquiv.toMonoidHom.comp κC).comp (inclusion hYS)
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hact (y : Y) (w : s.space.toSubmodule) : j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hYS y)))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hYS y) w
  let βT := β.comp (inclusion (show Z d.radical a ≤ Y from le_sup_right))
  have hcard : Nat.card βT.range=Nat.card E.Carrier := by
    have hmark : βT.ker=(Q d.radical z).subgroupOf (Z d.radical a) := by
      ext x
      change e.groupEquiv (κC (inclusion hYS (inclusion le_sup_right x)))=1 ↔ x.val ∈ Q d.radical z
      rw [e.groupEquiv.map_eq_one_iff]
      have heq : κC (inclusion hYS (inclusion le_sup_right x))=1 ↔
          inclusion hYS (inclusion le_sup_right x) ∈ κ.ker := Subtype.ext_iff
      rw [heq]
      constructor
      · intro hx
        exact hκQ ▸ mem_map_of_mem (stabilizer d.radical z).subtype hx
      · intro hx
        obtain ⟨y,hy,hyx⟩ := hκQ.symm ▸ hx
        have he : y=inclusion hYS (inclusion le_sup_right x) := Subtype.ext hyx
        exact he ▸ hy
    rw [←index_ker,hmark]
    exact hi.trans hFc.symm
  have hactT (x : Z d.radical a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (βT x) w))=x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ :=
    hact (inclusion le_sup_right x) w
  obtain ⟨hd,hrootquad⟩ := critical_root_coordinates_of_reciprocal_index_field path hpos hCa hFl
    σ p he j hj hjr βT hactT hcard (hi'.trans hFc.symm)
  have hcomm : ⁅Z d.radical a,j.range⁆ ≤ Z d.radical a := by
    rw [hjr]
    exact (commutator_mono le_rfl (U_le_Z z)).trans (critical_commutator_le_start_seed path)
  have hcent : Y ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    hYQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)))
  have hbound := TrappedRootComparison.embedded_root_hyperplane_le_commutator hFl p he j hj Y
    (Z d.radical a) le_sup_right β hact hcard hd hrootquad hcomm hcent
    (by rw [hjr]; exact le_bot_iff.mp ((commutator_mono (commutator_mono hUA le_rfl) le_rfl).trans_eq hquad))
    (by rw [hjr]; exact hUA.trans hAn) (by rwa [hjr])
  rw [hjr] at hbound
  have hDU : D ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans ((centralizer_le ((U_le_Z z).trans (Z_le_stabilizer d.radical z))).trans
      (Subgroup.centralizer_le_normalizer _))
  have hAX : X d.radical z ⊓ Q d.radical a ≤
      X d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [←hCa]
    exact inf_le_inf_left _ inf_le_right
  have hle : ⁅Z d.radical v,A⁆ ≤
      ⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ :=
    (commutator_mono le_sup_left hAX).trans
      (commutator_fixed_supplement_bound _ _ _ _ _ hsplit hDU hDY le_sup_right)
  exact ((commutator_mono le_rfl
    (inf_le_inf_right _ ((U_le_Z z).trans hZX))).trans hle).trans hbound


/-- The full starting radius cannot be trapped two steps before the critical
endpoint. This is the nontrapping clause of MS93 (5.8), with no additional
intersection, conjugation or fixed-layer premise. -/
theorem Input.replacement_radius_not_trapped
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t) :
    ¬ V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
  intro htrap
  obtain ⟨hA,hAQ,hbound,x,u,y,hx,htwist,hiB,hut,hy,haw,hvw,htrapv,hn,
      hi,hi',hU,hZ,hmap,hjoin,hfixed,hinv,hcomm,hback,hwhole,hwholeBack,hcard,hnot,
      hv,hcritical,hnewQ,hnewC⟩ :=
    h.replacement_trapped_radius_whole_commutator_configuration d path hb hat hfirst htrap
  let v := act d.radical y u
  have hle := h.replacement_trapped_root_commutator_le_critical d path hb haw hvw hn htrapv
  have hYS : Z d.radical v ≤ stabilizer d.radical (act d.radical x z) :=
    Z_le_stabilizer_of_dist_le v (geometry.exists_critical v hv) hcritical.1.le
  have hYback : Z d.radical (act d.radical x⁻¹ v) ≤ stabilizer d.radical z := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hYS
    have hZmap : (Z d.radical v).map (MulAut.conj x).toMonoidHom =
        Z d.radical (act d.radical x⁻¹ v) := by rw [Z_act d.radical x⁻¹ v,inv_inv]
    have hSmap : (stabilizer d.radical (act d.radical x z)).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical z := by
      have hs := stabilizer_act d.radical x⁻¹ (act d.radical x z)
      rw [inv_inv,←act_mul,mul_inv_cancel,act_one] at hs
      exact hs.symm
    rwa [hZmap,hSmap] at hh
  have hTS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hwholeLe : ⁅Z d.radical (act d.radical x⁻¹ v),U d.radical z⁆ ≤
      ⁅Z d.radical a,U d.radical z⁆ := by
    rw [←hwholeBack]
    exact hle
  have hfix := h.replacement_moving_fixed_antitone_of_commutator_le d geometry hb path.end_color
    (Z d.radical (act d.radical x⁻¹ v)) (Z d.radical a) hYback hTS hwholeLe
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hAC : U d.radical z ⊓ Q d.radical a ≤
      centralizer (Z d.radical (act d.radical x⁻¹ v) : Set (FreeAmalgam d.radical)) := by
    intro r hr
    have hrC : r ∈ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
      have hh : r ∈ C d.radical a := hCa.symm ▸ hr.2
      exact hh.2
    exact (hfix ⟨hr.1,hrC⟩).2
  have hz : ⁅Z d.radical (act d.radical x⁻¹ v),U d.radical z ⊓ Q d.radical a⁆=⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hAC)
  exact hnot (hback ▸ hz ▸ bot_le)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
