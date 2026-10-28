module
public import Theory.Representation.SymplecticFourOrthogonalCover.HyperplaneMovement

/-!
# A quadratic hyperplane comparison with an independent root

The root actor and the moving actor use one full cover and the same ambient
marking, but the moving actor need not contain the root. If its displacement
escapes the root displacement joined with its hyperplane displacement, that
hyperplane commutator lies in the literal root commutator and has order at
most the field order.

The comparison target contains the entire root-point preimage. This follows
from `Roots.cover_root_geometry` and a span induction into the root
commutator, including the covering kernel. Centralization of that actual
commutator supplies point fixation. No central attachment is discarded.

The scalar and standard-coordinate arguments below retain the local proofs
of HyperplaneMovement with this stronger comparison target and the joint
containment/cardinality conclusion. Existing public helper contracts are
unchanged. Source: MS93 (3.3)(ii), used in (5.12)(1), printed pp.867,924.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.TwoLocalCover
open scoped commutatorElement IsMulCommutative
namespace Representation.SymplecticFourOrthogonalCover.IndependentRootComparison
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
section Cover
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := F)) W}

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem point_radical_of_hyperplane_movement (g : Sp F)
    (hfix : g • e (F := F) 0=e 0)
    (hmove : ∀ v : Vector F, v (.inr 0)=0 → g • v-v ∈ point F) :
    g ∈ pointRadicalAmbient := by
  let g' : pointLocal (F := F) := ⟨g,(mem_pointLocal_iff_fixed g).mpr hfix⟩
  refine ⟨g',?_,rfl⟩
  change pointQuotient g'=1
  apply Subtype.ext
  ext i j
  have hj : (Pi.single (middleIndex j) (1:F) : Vector F) (.inr 0)=0 := by
    fin_cases j <;> simp [middleIndex]
  have hm := (mem_point_iff _).mp (hmove (Pi.single (middleIndex j) 1) hj)
  have he : ((g • (Pi.single (middleIndex j) (1:F) : Vector F)-Pi.single (middleIndex j) 1 : Vector F))
      (middleIndex i)=0 := by
    fin_cases i
    · exact hm.1
    · exact hm.2 1
  change pointQuotientMatrix g' i j=(1 : Matrix (Fin 2) (Fin 2) F) i j
  fin_cases i <;> fin_cases j <;>
    simpa [pointQuotientMatrix,middleIndex,Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Matrix.mulVec_single,
      g',sub_eq_zero] using he

/-- In a full central cover, a quadratic hyperplane action whose whole
displacement escapes the comparison subgroup lies in the point radical; its commutator has
order at most the field size. -/
private theorem embedded_standard_hyperplane_comparison
    (hF : 2 < Nat.card F)
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
    (⁅Y,A⁆ ≤ (((point F).restrictScalars (ZMod 2)).comap p.toLinearMap).toAddSubgroup.toSubgroup.map j) ∧
      Nat.card (⁅Y,A⁆ : Subgroup G) ≤ Nat.card F := by
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
  have hcontain : ⁅Y,A⁆ ≤ (((point F).restrictScalars (ZMod 2)).comap p.toLinearMap).toAddSubgroup.toSubgroup.map j := by
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
  have hpβ (y : Y) : (β y).val ∈ pointRadicalAmbient := by
    apply point_radical_of_hyperplane_movement _
      (hfix y _ (Submodule.subset_span (Set.mem_singleton _)))
    intro v hv
    have hvH : v ∈ H := by
      intro w hw
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
      simp [form_apply,Theory.SpecificGroups.SymplecticFour.e,hv]
    exact hle ((le_iSup (fun y : α.range => H.map (symplecticNatural 2 y.val-LinearMap.id))
      ⟨α y,⟨y,rfl⟩⟩) ⟨v,hvH,rfl⟩)
  obtain ⟨s,hs,hmove,_⟩ := cover_point_overlap hF p hp
  let f : Multiplicative F →* G := j.comp s.toAddMonoidHom.toMultiplicative
  have hf : Function.Injective f := by
    intro x y he
    have hxy := congrArg (fun v => (p v) (.inl 0)) (congrArg Multiplicative.toAdd (hj he))
    simpa [hs,ClassicalOrthogonal.e] using hxy
  have hcomm : ⁅Y,A⁆ ≤ f.range := by
    apply commutator_le.mpr
    intro y hy a ha
    obtain ⟨w,rfl⟩ := hAr ha
    have hw := (hA w.toAdd).mp ha
    have hw0 : (p w.toAdd) (.inr 0)=0 := by
      have hh := hw (e 0) (Submodule.subset_span (Set.mem_singleton _))
      simpa [form_apply,Theory.SpecificGroups.SymplecticFour.e] using hh
    obtain ⟨t,ht⟩ := hmove (β ⟨y,hy⟩) (hpβ ⟨y,hy⟩) w.toAdd hw0
    refine ⟨Multiplicative.ofAdd t,?_⟩
    change j (Multiplicative.ofAdd (s t))=_
    rw [ht,hdisp]
    rfl
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact ⟨hcontain,(Nat.card_le_card_of_injective (inclusion hcomm) (inclusion_injective _)).trans_eq
    ((Nat.card_range_of_injective hf).trans (Nat.card_congr Multiplicative.toAdd))⟩

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

/-- The root and moving actors have one marking but no containment relation.
Failure of the comparison with the root displacement forces the full
hyperplane commutator into that displacement, with order at most q. -/
theorem embedded_independent_root_comparison
    (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (S T Y : Subgroup G) (hTS : T ≤ S) (hYS : Y ≤ S) (β : S →* L (K := F))
    (hact : ∀ (s : S) (w : W), j (Multiplicative.ofAdd (σ (β s) w)) =
      s.val*j (Multiplicative.ofAdd w)*s.val⁻¹)
    (hcard : Nat.card (β.comp (inclusion hTS)).range = Nat.card F)
    (hd : Module.finrank F (displacementSpace
      ((β.comp (inclusion hTS)).range.map (commutator (Sp F)).subtype)) = 1)
    (hrootquad : ∀ x ∈ (β.comp (inclusion hTS)).range.map (commutator (Sp F)).subtype,
      ∀ y ∈ (β.comp (inclusion hTS)).range.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hcent : Y ≤ centralizer ((⁅T,j.range⁆ : Subgroup G) : Set G))
    (hquad : ⁅⁅j.range ⊓ centralizer (T : Set G),Y⁆,Y⁆ = ⊥)
    (hbad : ¬ ⁅Y,j.range⁆ ≤ ⁅T,j.range⁆ ⊔ ⁅Y,j.range ⊓ centralizer (T : Set G)⁆) :
    ⁅Y,j.range ⊓ centralizer (T : Set G)⁆ ≤ ⁅T,j.range⁆ ∧
      Nat.card (⁅Y,j.range ⊓ centralizer (T : Set G)⁆ : Subgroup G) ≤ Nat.card F := by
  have hcard' : Nat.card ((β.comp (inclusion hTS)).range.map (commutator (Sp F)).subtype)=Nat.card F := by
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
  have hact' (s : S) (w : W) : j' (Multiplicative.ofAdd (σ (β' s) w)) =
      s.val*j' (Multiplicative.ofAdd w)*s.val⁻¹ := by
    change j (Multiplicative.ofAdd (σ gl⁻¹ (σ (gl*β s*gl⁻¹) w)))=_
    simp only [map_mul,Module.End.mul_apply,inv_self_apply]
    exact hact s (σ gl⁻¹ w)
  have hT' : ((β'.comp (inclusion hTS)).range.map (commutator (Sp F)).subtype)=RootSubgroup.group 0 := by
    rw [←hg]
    ext x
    constructor
    · rintro ⟨_,⟨t,rfl⟩,rfl⟩
      exact ⟨(β (inclusion hTS t)).val,mem_map_of_mem _ ⟨t,rfl⟩,rfl⟩
    · rintro ⟨_,⟨_,⟨t,rfl⟩,rfl⟩,rfl⟩
      exact ⟨β' (inclusion hTS t),⟨t,rfl⟩,rfl⟩
  have hroot (w : W) (hw : p w ∈ point F) : j' (Multiplicative.ofAdd w) ∈ ⁅T,j'.range⁆ :=
    standard_root_commutator_preimage hF p hp j' S T hTS β' hact' hT' w hw
  let βY := β'.comp (inclusion hYS)
  have hactY (y : Y) (w : W) : j' (Multiplicative.ofAdd (σ (βY y) w)) =
      y.val*j' (Multiplicative.ofAdd w)*y.val⁻¹ := hact' (inclusion hYS y) w
  have hfix (y : Y) (v : Vector F) (hv : v ∈ point F) : (βY y).val • v=v := by
    obtain ⟨w,rfl⟩ := hp.1 v
    have he : σ (βY y) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj'
      rw [hactY,←hcent y.property _ (hjr ▸ hroot w hv),mul_inv_cancel_right]
    exact (LinearMap.congr_fun (p.isIntertwining' (βY y)) w).symm.trans (congrArg p he)
  have hh := embedded_standard_hyperplane_comparison hF p hp j' hj'
    Y (j'.range ⊓ centralizer (T : Set G))
    (⁅T,j'.range⁆ ⊔ ⁅Y,j'.range ⊓ centralizer (T : Set G)⁆) βY hactY
    (fun w => by
      rw [mem_inf,standard_root_fixed_iff p hp j' hj' S T hTS β' hact' hT']
      exact and_iff_right ⟨_,rfl⟩)
    inf_le_left (fun w hw => mem_sup_left (hroot w hw)) hfix
    (by rwa [hjr]) le_sup_right (by rwa [hjr])
  rw [←hjr]
  refine ⟨hh.1.trans ?_,hh.2⟩
  rintro _ ⟨w,hw,rfl⟩
  exact hroot w.toAdd hw

end Cover
end Representation.SymplecticFourOrthogonalCover.IndependentRootComparison

