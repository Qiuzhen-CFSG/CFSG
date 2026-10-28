module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourComplement

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourFullSaturation

/-!
# Full-cover root selection in the escaping attachment comparison

When a complete fixed attachment has order q, the universal orthogonal cover
maps bijectively to the original moving group. Its fixed spaces, movements
and covering kernel therefore retain their field structure. In particular,
the hyperplane movement either contains the entire attachment or meets it
trivially. The proof keeps the original embedding and the complete kernel.

A nonzero vector in the root-movement intersection outside the attachment
and the section-centralizer complement has coordinates (a e₀,b), with a and
b nonzero. The long-root parameter (a/b)² gives a nontrivial displacement
line through that vector. Field linearity puts all this root's displacements
in the hyperplane movement. Conjugation transports the calculation through
any supplied plane marking, without choosing a different hyperplane.

For the actual critical configuration, the escaping-centralizer factorization
moves the selected root element into the opposite Z-centralizer. The full
midpoint supplement extends its displacement containment from U to Z.
The opposite-field value-escape theorem then contradicts noncontainment of
the first attachment. Thus the marked comparison proves A ≤ [X,Z′].

The source application retains the preceding order, nontrivial-intersection,
noncontainment and disjoint-complement premises explicitly. Their construction
with this same marked hyperplane, the remaining attachment equality and
nonescaping branch of (4), source (5)/(6), and n=2 with the block conclusion
remain with the saturated-distance-two assembly. The Chapter11 adapters
use the literal original quotient and action maps.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(4), printed p.875. Private covering and subgroup transports
adapt SourceFourFullIntersection, SourceFourHyperplane and SourceFourComplement;
the root-coordinate calculation follows the checked orthogonal-cover Roots API.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement IsMulCommutative

private theorem full_cover_quotient
    {F W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hc : Nat.card p.toLinearMap.ker=Nat.card F) :
    ∃ f : binaryAction.IntertwiningMap σ, Function.Bijective f ∧
      ∀ v, p (f v)=binaryProjection v := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  let k : F → p.toLinearMap.ker := fun t => ⟨f (0,t),hpf (0,t)⟩
  have hs : Function.Surjective k := by
    intro w
    obtain ⟨v,hv⟩ := hf w.val
    have hv1 : v.1=0 := (hpf v).symm.trans (by rw [hv]; exact w.property)
    exact ⟨v.2,Subtype.ext (by change f (0,v.2)=w.val; rw [←hv1,hv])⟩
  have hi : Function.Injective k := (Nat.bijective_iff_surjective_and_card _).mpr ⟨hs,hc.symm⟩ |>.1
  refine ⟨f,⟨?_,hf⟩,hpf⟩
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro v hv
  have hv1 : v.1=0 := (hpf v).symm.trans (by rw [show f v=0 from hv,map_zero])
  have hz : k v.2=k 0 := Subtype.ext (by
    change f (0,v.2)=f (0,0)
    rw [show (0,v.2)=v from Prod.ext hv1.symm rfl,show f v=0 from hv]
    exact (map_zero f).symm)
  exact Prod.ext hv1 (hi hz)

private theorem embedded_linear_movement
    {F V G J : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Group G] [Group J] (ρ : Representation F J V)
    (j : Multiplicative V →* G) (B X : Subgroup G)
    (β : B →* J) (hact : ∀ b : B, ∀ v : V,
      j (Multiplicative.ofAdd (ρ (β b) v))=b.val*j (Multiplicative.ofAdd v)*b.val⁻¹)
    (D : Submodule F V) (hX : D.toAddSubgroup.toSubgroup.map j=X) :
    ∃ E : Submodule F V, E.toAddSubgroup.toSubgroup.map j=⁅B,X⁆ := by
  let E : Submodule F V := ⨆ b : B, D.map (ρ (β b)-LinearMap.id)
  refine ⟨E,le_antisymm ?_ ?_⟩
  · rintro x ⟨v,hv,rfl⟩
    change v.toAdd ∈ E at hv
    change j (Multiplicative.ofAdd v.toAdd) ∈ _
    refine Submodule.iSup_induction _ (motive := fun w => j (Multiplicative.ofAdd w) ∈ ⁅B,X⁆) hv ?_ ?_ ?_
    · intro b v hv
      obtain ⟨w,hw,rfl⟩ := hv
      change j (Multiplicative.ofAdd (ρ (β b) w-w)) ∈ _
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      exact commutator_mem_commutator b.property (hX ▸ ⟨_,hw,rfl⟩)
    · exact (map_one j).symm ▸ one_mem _
    · intro u v hu hv
      simpa only [ofAdd_add,map_mul] using (⁅B,X⁆).mul_mem hu hv
  · apply commutator_le.mpr
    intro b hb x hx
    obtain ⟨v,hv,rfl⟩ := hX.symm ▸ hx
    refine ⟨Multiplicative.ofAdd (ρ (β ⟨b,hb⟩) v.toAdd-v.toAdd),?_,?_⟩
    · change ρ (β ⟨b,hb⟩) v.toAdd-v.toAdd ∈ E
      exact (le_iSup (fun b : B => D.map (ρ (β b)-LinearMap.id)) ⟨b,hb⟩) ⟨v.toAdd,hv,rfl⟩
    · rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl


private theorem embedded_linear_fixed
    {F V G J : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Group G] [Group J] (ρ : Representation F J V)
    (j : Multiplicative V →* G) (hj : Function.Injective j) (B : Subgroup G)
    (β : B →* J) (hact : ∀ b : B, ∀ v : V,
      j (Multiplicative.ofAdd (ρ (β b) v))=b.val*j (Multiplicative.ofAdd v)*b.val⁻¹) :
    ∃ D : Submodule F V, D.toAddSubgroup.toSubgroup.map j=
      j.range ⊓ centralizer (B : Set G) := by
  let D : Submodule F V := ⨅ b : B, LinearMap.ker (ρ (β b)-LinearMap.id)
  refine ⟨D,le_antisymm ?_ ?_⟩
  · rintro x ⟨v,hv,rfl⟩
    change v.toAdd ∈ D at hv
    refine ⟨⟨v,rfl⟩,fun b hb => ?_⟩
    have he : ρ (β ⟨b,hb⟩) v.toAdd=v.toAdd :=
      sub_eq_zero.mp ((iInf_le (fun b : B => LinearMap.ker (ρ (β b)-LinearMap.id)) ⟨b,hb⟩) hv)
    have hh := congrArg (fun w => j (Multiplicative.ofAdd w)) he
    rw [hact,mul_inv_eq_iff_eq_mul] at hh
    exact hh
  · rintro x ⟨⟨v,rfl⟩,hv⟩
    refine ⟨v,?_,rfl⟩
    change v.toAdd ∈ D
    simp only [D,Submodule.mem_iInf]
    intro b
    change ρ (β b) v.toAdd-v.toAdd=0
    apply sub_eq_zero.mpr
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hact,ofAdd_toAdd,hv b.val b.property,mul_inv_cancel_right]

private theorem embedded_subspace_card
    {F V G : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Group G]
    (j : Multiplicative V →* G) (hj : Function.Injective j) (D : Submodule F V) :
    Nat.card (D.toAddSubgroup.toSubgroup.map j)=Nat.card F^Module.finrank F D := by
  rw [card_map_of_injective hj]
  let e : D.toAddSubgroup.toSubgroup ≃ D :=
    { toFun := fun x => ⟨x.val.toAdd,x.property⟩
      invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := F)]

private theorem full_cover_embedding_with_kernel
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hc : Nat.card p.toLinearMap.ker=Nat.card F)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (P T : Subgroup G) (β : P →* L (K := F)) (γ : T →* L (K := F))
    (hβ : ∀ x : P, ∀ w : W, j (Multiplicative.ofAdd (σ (β x) w))=
      x.val*j (Multiplicative.ofAdd w)*x.val⁻¹)
    (hγ : ∀ x : T, ∀ w : W, j (Multiplicative.ofAdd (σ (γ x) w))=
      x.val*j (Multiplicative.ofAdd w)*x.val⁻¹) :
    ∃ j₀ : Multiplicative (Space (K := F)) →* G,
      Function.Injective j₀ ∧ j₀.range=j.range ∧
      projection.toLinearMap.ker.toAddSubgroup.toSubgroup.map j₀=
        p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j ∧
      (∀ x : P, ∀ v : Space (K := F), j₀ (Multiplicative.ofAdd (action (β x) v))=
        x.val*j₀ (Multiplicative.ofAdd v)*x.val⁻¹) ∧
      (∀ x : T, ∀ v : Space (K := F), j₀ (Multiplicative.ofAdd (action (γ x) v))=
        x.val*j₀ (Multiplicative.ofAdd v)*x.val⁻¹) := by
  obtain ⟨f,hf,hpf⟩ := full_cover_quotient p hp hc
  let j₀ : Multiplicative (Space (K := F)) →* G :=
    j.comp f.toLinearMap.toAddMonoidHom.toMultiplicative
  have hj₀ : Function.Injective j₀ := by
    intro v w he
    exact Multiplicative.toAdd.injective (hf.1 (congrArg Multiplicative.toAdd (hj he)))
  have hr : j₀.range=j.range := by
    apply le_antisymm
    · rintro x ⟨v,rfl⟩; exact ⟨_,rfl⟩
    · rintro x ⟨w,rfl⟩
      obtain ⟨v,hv⟩ := hf.2 w.toAdd
      exact ⟨Multiplicative.ofAdd v,congrArg j (congrArg Multiplicative.ofAdd hv)⟩
  have hβ₀ (x : P) (v : Space (K := F)) :
      j₀ (Multiplicative.ofAdd (action (β x) v))=
        x.val*j₀ (Multiplicative.ofAdd v)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (f (binaryAction (β x) v)))=_
    rw [f.isIntertwining,hβ]
    rfl
  have hγ₀ (x : T) (v : Space (K := F)) :
      j₀ (Multiplicative.ofAdd (action (γ x) v))=
        x.val*j₀ (Multiplicative.ofAdd v)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (f (binaryAction (γ x) v)))=_
    rw [f.isIntertwining,hγ]
    rfl
  let A : Submodule F (Space (K := F)) := projection.toLinearMap.ker
  have hA : A.toAddSubgroup.toSubgroup.map j₀=
      p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨Multiplicative.ofAdd (f v.toAdd),(hpf v.toAdd).trans hv,rfl⟩
    · rintro x ⟨w,hw,rfl⟩
      obtain ⟨v,hv⟩ := hf.2 w.toAdd
      refine ⟨Multiplicative.ofAdd v,?_,congrArg j (congrArg Multiplicative.ofAdd hv)⟩
      change projection v=0
      exact (hpf v).symm.trans (by rw [hv]; exact hw)
  exact ⟨j₀,hj₀,hr,hA,hβ₀,hγ₀⟩

private theorem full_cover_fixed_movement_kernel_power
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hc : Nat.card p.toLinearMap.ker=Nat.card F)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (P T : Subgroup G) (β : P →* L (K := F)) (γ : T →* L (K := F))
    (hβ : ∀ x : P, ∀ w : W, j (Multiplicative.ofAdd (σ (β x) w))=
      x.val*j (Multiplicative.ofAdd w)*x.val⁻¹)
    (hγ : ∀ x : T, ∀ w : W, j (Multiplicative.ofAdd (σ (γ x) w))=
      x.val*j (Multiplicative.ofAdd w)*x.val⁻¹) :
    ∃ r : ℕ, Nat.card (⁅T,j.range ⊓ centralizer (P : Set G)⁆ ⊓
      p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j : Subgroup G)=Nat.card F^r := by
  obtain ⟨j₀,hj₀,hr,hA,hβ₀,hγ₀⟩ := full_cover_embedding_with_kernel p hp hc j hj P T β γ hβ hγ
  obtain ⟨D,hD⟩ := embedded_linear_fixed action j₀ hj₀ P β hβ₀
  obtain ⟨M,hM⟩ := embedded_linear_movement action j₀ T
    (j₀.range ⊓ centralizer (P : Set G)) γ hγ₀ D hD
  let A : Submodule F (Space (K := F)) := projection.toLinearMap.ker
  refine ⟨Module.finrank F (M ⊓ A : Submodule F (Space (K := F))),?_⟩
  rw [←hr,←hM,←hA,←Subgroup.map_inf _ _ j₀ hj₀]
  exact embedded_subspace_card j₀ hj₀ (M ⊓ A)

private theorem root_element_for_vector
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (v : Space (K := F))
    (hv : v ∈ Roots.firstPreimage) (hv1 : v.1 ≠ 0) (hv2 : v.2 ≠ 0) :
    ∃ t : F, ∃ u : Space (K := F),
      action (Roots.element hF t) u-u=v ∧
      ∀ w : Space (K := F), action (Roots.element hF t) w-w ∈ Submodule.span F {v} := by
  obtain ⟨a,ha⟩ := (Roots.mem_firstPreimage v).mp hv
  have ha0 : a ≠ 0 := by
    intro he
    apply hv1
    rw [←ha,he,zero_smul]
  let t := (a/v.2)^2
  let u : Space (K := F) := ((v.2^2/a) • ClassicalOrthogonal.f 0,0)
  have hs : Roots.sqrt t=a/v.2 := (frobeniusEquiv F 2).symm_apply_apply (a/v.2)
  have he : action (Roots.element hF t) u-u=v := by
    rw [Roots.displacement]
    apply Prod.ext
    · rw [←ha]
      change (_ : F) • (t • ClassicalOrthogonal.e 0)=_
      simp only [u,ClassicalOrthogonal.f,Pi.smul_apply,Pi.single_eq_same,
        smul_eq_mul,mul_one,smul_smul]
      congr 1
      dsimp only [t]
      field_simp
    · change (_ : F) * Roots.sqrt t=v.2
      rw [hs]
      simp only [u,ClassicalOrthogonal.f,Pi.smul_apply,Pi.single_eq_same,
        smul_eq_mul,mul_one]
      field_simp
  have ht : t ≠ 0 := pow_ne_zero 2 (div_ne_zero ha0 hv2)
  have hv0 : v ≠ 0 := fun hh => hv1 (congrArg Prod.fst hh)
  have hline : Roots.rootDisplacement hF t=Submodule.span F {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (Roots.rootDisplacement_dimension hF t ht) ⟨u,he⟩ hv0
  refine ⟨t,u,he,fun w => ?_⟩
  rw [←hline]
  exact ⟨w,rfl⟩

section RootSelection
open Matrix Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := F)) W}
private theorem standard_root_preimage_displacement
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


omit [Algebra (ZMod 2) F] in
private theorem point_correction (u v z : F) (x : Natural (K := F))
    (hx : x (.inr 0)=0) : correction (pointRadicalElement u v z).val x = 0 := by
  simp [correction, quadraticCocycle, transposeSp, pointRadicalElement, pointRadicalMatrix,
    rowQuadratic, Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks, hx]

private theorem point_hyperplane_displacement (g : L (K := F))
    (hg : g.val ∈ ((pointRadical (F := F)).map pointLocal.subtype)) (x : Space (K := F)) (hx : x.1 (.inr 0)=0) :
    ∃ t : F, binaryAction g x-x=(t • ClassicalOrthogonal.e 0,0) := by
  obtain ⟨b,hb,he⟩ := hg
  have hb' := pointRadical_eq_element b hb
  have he' : g.val=(pointRadicalElement
      (b.val.val (.inl 1) (.inr 0)) (b.val.val (.inr 1) (.inr 0))
      (b.val.val (.inl 0) (.inr 0))).val := he.symm.trans (congrArg Subtype.val hb')
  let u := b.val.val (.inl 1) (.inr 0)
  let v := b.val.val (.inr 1) (.inr 0)
  let z := b.val.val (.inl 0) (.inr 0)
  refine ⟨v*x.1 (.inl 1)+u*x.1 (.inr 1),?_⟩
  change action g x-x=_
  rw [action_apply]
  change (g.val.val *ᵥ x.1,x.2+correction g.val x.1)-x=_
  rw [he',point_correction u v z x.1 hx]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec,
      dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,hx,ClassicalOrthogonal.e,u,v,add_assoc]
  · simp


private theorem universal_root_selection
    (hF : 2 < Nat.card F)
    (j : Multiplicative (Space (K := F)) →* G) (hj : Function.Injective j)
    (Y P B T : Subgroup G) (hPY : P ≤ Y) (hTY : T ≤ Y)
    (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (v : Space (K := F)), j (Multiplicative.ofAdd (action (β y) v))=
      y.val*j (Multiplicative.ofAdd v)*y.val⁻¹)
    (hroot : (β.comp (inclusion hPY)).range.map (commutator (Sp F)).subtype=RootSubgroup.group 0)
    (hplane : ((commutator (Sp F)).subtype.comp β).range=planeRadicalAmbient)
    (hfix : ∀ v : Space (K := F), j (Multiplicative.ofAdd v) ∈ centralizer (P : Set G) ↔ v.1 (.inr 0)=0)
    (hmem : ∀ b : G, b ∈ B ↔ b ∈ Y ∧ ∀ x ∈ j.range ⊓ centralizer (P : Set G), ⁅b,x⁆ ∈ ⁅P,j.range⁆)
    (hne : (⁅T,j.range ⊓ centralizer (P : Set G)⁆ ⊓ ⁅P,j.range⁆ : Subgroup G) ≠ ⊥)
    (hdis : Disjoint ⁅T,j.range ⊓ centralizer (P : Set G)⁆
      (projection.toLinearMap.ker.toAddSubgroup.toSubgroup.map j))
    (hcomp : Disjoint ⁅T,j.range ⊓ centralizer (P : Set G)⁆
      ⁅j.range ⊓ centralizer (P : Set G),B⁆) :
    ∃ y ∈ P, (∃ u ∈ j.range, ⁅y,u⁆ ≠ 1) ∧
      ∀ u ∈ j.range, ⁅y,u⁆ ∈ ⁅T,j.range ⊓ centralizer (P : Set G)⁆ := by
  let M := ⁅T,j.range ⊓ centralizer (P : Set G)⁆
  let N := Roots.firstPreimage.toAddSubgroup.toSubgroup.map j
  have hHN : ⁅P,j.range⁆ ≤ N := by
    apply commutator_le.mpr
    rintro y hy _ ⟨w,rfl⟩
    obtain ⟨t,ht⟩ := (RootSubgroup.mem_group_iff 0 _).mp
      (show (β ⟨y,hPY hy⟩).val ∈ RootSubgroup.group 0 from
        hroot ▸ mem_map_of_mem _ ⟨⟨y,hy⟩,rfl⟩)
    have he : β ⟨y,hPY hy⟩=Roots.element hF t := Subtype.ext ht.symm
    refine ⟨Multiplicative.ofAdd (action (β ⟨y,hPY hy⟩) w.toAdd-w.toAdd),?_,?_⟩
    · change action (β ⟨y,hPY hy⟩) w.toAdd-w.toAdd ∈ Roots.firstPreimage
      rw [he]
      exact Roots.rootDisplacement_le_firstPreimage hF t ⟨w.toAdd,rfl⟩
    · rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
  have hN (v : Space (K := F)) (hv : v ∈ Roots.firstPreimage) :
      j (Multiplicative.ofAdd v) ∈ ⁅P,j.range⁆ :=
    standard_root_preimage_displacement hF binaryProjection binaryProjection_isCover
      j Y P hPY β hact hroot v hv
  have hhorizontal (a : F) : j (Multiplicative.ofAdd (a • ClassicalOrthogonal.e 0,0)) ∈
      ⁅j.range ⊓ centralizer (P : Set G),B⁆ := by
    let b : L (K := F) := ⟨(pointRadicalElement a 0 0).val,
      by rw [LargeField.commutator_eq_top hF]; trivial⟩
    have hbplane : b.val ∈ planeRadicalAmbient := by
      apply (SymplecticConjugatePair.mem_planeRadical_iff _).mpr
      refine ⟨⟨!![0,a;a,0],by ext i k; fin_cases i <;> fin_cases k <;> rfl⟩,?_⟩
      apply Subtype.ext
      ext i k
      fin_cases i <;> fin_cases k <;> simp [b,Plane.shearSp,pointRadicalElement,
        pointRadicalMatrix,Matrix.fromBlocks]
    obtain ⟨y,hy⟩ := (show b.val ∈ ((commutator (Sp F)).subtype.comp β).range from hplane.symm ▸ hbplane)
    have hβ : β y=b := Subtype.ext hy
    have hyB : y.val ∈ B := by
      apply (hmem y.val).mpr
      refine ⟨y.property,?_⟩
      rintro _ ⟨⟨w,rfl⟩,hw⟩
      have hw0 := (hfix w.toAdd).mp hw
      obtain ⟨s,hs⟩ := point_hyperplane_displacement b
        (mem_map_of_mem _ (pointRadicalElement_mem a 0 0)) w.toAdd hw0
      have hh := hN (action (β y) w.toAdd-w.toAdd) (by
        rw [hβ]
        change binaryAction b w.toAdd-w.toAdd ∈ Roots.firstPreimage
        rw [hs]
        exact (Roots.mem_firstPreimage _).mpr ⟨s,rfl⟩)
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact] at hh
      exact hh
    let w : Space (K := F) := (ClassicalOrthogonal.f 1,0)
    have hval : action b w-w=(a • ClassicalOrthogonal.e 0,0) := by
      rw [action_apply]
      apply Prod.ext
      · ext i
        fin_cases i <;> simp [b,w,pointRadicalElement,pointRadicalMatrix,Matrix.fromBlocks,
          ClassicalOrthogonal.e,ClassicalOrthogonal.f]
      · change (0+correction (pointRadicalElement a 0 0).val (ClassicalOrthogonal.f 1))-0=0
        rw [point_correction a 0 0 (ClassicalOrthogonal.f 1) (by simp [ClassicalOrthogonal.f])]
        simp
    have hh : j (Multiplicative.ofAdd (a • ClassicalOrthogonal.e 0,0))=⁅y.val,j (Multiplicative.ofAdd w)⁆ := by
      rw [←hval,←hβ,ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
    rw [hh,commutator_comm]
    exact commutator_mem_commutator hyB ⟨⟨_,rfl⟩,(hfix w).mpr (by rfl)⟩
  obtain ⟨D,hD⟩ := embedded_linear_fixed action j hj P (β.comp (inclusion hPY))
    (fun y w => hact (inclusion hPY y) w)
  obtain ⟨E,hE⟩ := embedded_linear_movement action j T
    (j.range ⊓ centralizer (P : Set G)) (β.comp (inclusion hTY))
      (fun y w => hact (inclusion hTY y) w) D hD
  obtain ⟨x,hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨v,hv,hvx⟩ := hHN x.property.2
  have hvE : v.toAdd ∈ E := by
    obtain ⟨w,hw,he⟩ := (show x.val ∈ E.toAddSubgroup.toSubgroup.map j from hE.symm ▸ x.property.1)
    exact hj (he.trans hvx.symm) ▸ hw
  have hv1 : v.toAdd.1 ≠ 0 := by
    intro hz
    have hh : x.val ∈ M ⊓ projection.toLinearMap.ker.toAddSubgroup.toSubgroup.map j :=
      ⟨x.property.1,⟨v,hz,hvx⟩⟩
    exact hxne (Subtype.ext ((show x.val ∈ (⊥ : Subgroup G) from disjoint_iff.mp hdis ▸ hh)))
  have hv2 : v.toAdd.2 ≠ 0 := by
    intro hz
    obtain ⟨a,ha⟩ := (Roots.mem_firstPreimage v.toAdd).mp hv
    have hh : x.val ∈ M ⊓ ⁅j.range ⊓ centralizer (P : Set G),B⁆ :=
      ⟨x.property.1,by rw [←hvx,show v=Multiplicative.ofAdd (a • ClassicalOrthogonal.e 0,0) from
        congrArg Multiplicative.ofAdd (Prod.ext ha.symm hz)]; exact hhorizontal a⟩
    exact hxne (Subtype.ext ((show x.val ∈ (⊥ : Subgroup G) from disjoint_iff.mp hcomp ▸ hh)))
  obtain ⟨t,u,hu,hline⟩ := root_element_for_vector hF v.toAdd hv hv1 hv2
  obtain ⟨_,⟨y,rfl⟩,hy⟩ := (show (Roots.element hF t).val ∈
      (β.comp (inclusion hPY)).range.map (commutator (Sp F)).subtype from
    hroot.symm ▸ (Roots.element_mem_group hF t))
  have hβ : β (inclusion hPY y)=Roots.element hF t := Subtype.ext hy
  have hdisp (w : Space (K := F)) :
      j (Multiplicative.ofAdd (action (Roots.element hF t) w-w))=⁅y.val,j (Multiplicative.ofAdd w)⁆ := by
    rw [←hβ,ofAdd_sub,map_div,div_eq_mul_inv,hact]
    rfl
  refine ⟨y.val,y.property,⟨j (Multiplicative.ofAdd u),⟨_,rfl⟩,?_⟩,?_⟩
  · rw [←hdisp,hu,ofAdd_toAdd,hvx]
    intro he
    exact hxne (Subtype.ext he)
  · rintro _ ⟨w,rfl⟩
    change ⁅y.val,j (Multiplicative.ofAdd w.toAdd)⁆ ∈ _
    rw [←hdisp,←hE]
    have hl : Submodule.span F {v.toAdd} ≤ E := Submodule.span_le.mpr
      (by intro z hz; rw [Set.mem_singleton_iff.mp hz]; exact hvE)
    exact ⟨Multiplicative.ofAdd (action (Roots.element hF t) w.toAdd-w.toAdd),hl (hline w.toAdd),rfl⟩
private theorem standard_root_image
    (_hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y P : Subgroup G) (hPY : P ≤ Y) (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hY : ((commutator (Sp F)).subtype.comp β).range=planeRadicalAmbient)
    (hpoint : P=Y ⊓ centralizer (j.range ⊓ centralizer (P : Set G) : Set G))
    (hfix : ∀ w : W, j (Multiplicative.ofAdd w) ∈ centralizer (P : Set G) ↔
      (p w) (.inr 0)=0) :
    (β.comp (inclusion hPY)).range.map (commutator (Sp F)).subtype=RootSubgroup.group 0 := by
  let ψ := (commutator (Sp F)).subtype.comp β
  apply le_antisymm
  · rintro _ ⟨_,⟨y,rfl⟩,rfl⟩
    rw [←PointRadicalAction.hyperplane_fixer]
    apply (mem_fixingSubgroup_iff _).mpr
    intro v hv
    obtain ⟨w,rfl⟩ := hp.1 v
    have hv0 : (p w) (.inr 0)=0 := by
      have he := hv (e 0) (Submodule.subset_span (Set.mem_singleton _))
      simpa [form_apply,Theory.SpecificGroups.SymplecticFour.e] using he
    have he : σ (β (inclusion hPY y)) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact]
      have hh := (hfix w).mpr hv0 y.val y.property
      change y.val*j (Multiplicative.ofAdd w)*y.val⁻¹=_
      rw [hh,mul_inv_cancel_right]
    have hh := congrArg p he
    rw [p.isIntertwining] at hh
    exact hh
  · intro a ha
    obtain ⟨r,rfl⟩ := (RootSubgroup.mem_group_iff 0 a).mp ha
    have hr : rootElement 0 r ∈ planeRadicalAmbient (F := F) := by
      apply (SymplecticConjugatePair.mem_planeRadical_iff _).mpr
      refine ⟨⟨!![r,0;0,0],by ext i k; fin_cases i <;> fin_cases k <;> rfl⟩,?_⟩
      apply Subtype.ext
      ext i k
      fin_cases i <;> fin_cases k <;>
        simp [Plane.shearSp,rootElement,rootMatrix,Matrix.fromBlocks,Matrix.single]
    obtain ⟨y,hy⟩ := (show rootElement 0 r ∈ ψ.range from hY.symm ▸ hr)
    have hyP : y.val ∈ P := by
      rw [hpoint]
      refine ⟨y.property,?_⟩
      rintro _ ⟨⟨w,rfl⟩,hw⟩
      have he : binaryNatural (β y) (p w.toAdd)=p w.toAdd := by
        change (ψ y).val *ᵥ p w.toAdd=p w.toAdd
        rw [hy,Roots.natural_root]
        simp only [(hfix w.toAdd).mp hw,mul_zero,zero_smul,add_zero]
      have hh := congrArg (fun v => j (Multiplicative.ofAdd v))
        (cover_fixed_of_projection_fixed p hp (β y) w.toAdd he)
      rw [hact,mul_inv_eq_iff_eq_mul] at hh
      exact hh.symm
    exact ⟨β y,⟨⟨y.val,hyP⟩,rfl⟩,hy⟩
private theorem full_cover_root_selection
    (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hc : Nat.card p.toLinearMap.ker=Nat.card F)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y P B T : Subgroup G) (hPY : P ≤ Y) (hTY : T ≤ Y)
    (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hplane : ((commutator (Sp F)).subtype.comp β).range=planeRadicalAmbient)
    (hpoint : P=Y ⊓ centralizer (j.range ⊓ centralizer (P : Set G) : Set G))
    (hfix : ∀ w : W, j (Multiplicative.ofAdd w) ∈ centralizer (P : Set G) ↔ (p w) (.inr 0)=0)
    (hmem : ∀ b : G, b ∈ B ↔ b ∈ Y ∧ ∀ x ∈ j.range ⊓ centralizer (P : Set G), ⁅b,x⁆ ∈ ⁅P,j.range⁆)
    (hne : (⁅T,j.range ⊓ centralizer (P : Set G)⁆ ⊓ ⁅P,j.range⁆ : Subgroup G) ≠ ⊥)
    (hdis : Disjoint ⁅T,j.range ⊓ centralizer (P : Set G)⁆
      (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j))
    (hcomp : Disjoint ⁅T,j.range ⊓ centralizer (P : Set G)⁆
      ⁅j.range ⊓ centralizer (P : Set G),B⁆) :
    ∃ y ∈ P, (∃ u ∈ j.range, ⁅y,u⁆ ≠ 1) ∧
      ∀ u ∈ j.range, ⁅y,u⁆ ∈ ⁅T,j.range ⊓ centralizer (P : Set G)⁆ := by
  obtain ⟨f,hf,hpf⟩ := full_cover_quotient p hp hc
  let j₀ : Multiplicative (Space (K := F)) →* G :=
    j.comp f.toLinearMap.toAddMonoidHom.toMultiplicative
  have hj₀ : Function.Injective j₀ := by
    intro v w he
    exact Multiplicative.toAdd.injective (hf.1 (congrArg Multiplicative.toAdd (hj he)))
  have hr : j₀.range=j.range := by
    apply le_antisymm
    · rintro x ⟨v,rfl⟩; exact ⟨_,rfl⟩
    · rintro x ⟨w,rfl⟩
      obtain ⟨v,hv⟩ := hf.2 w.toAdd
      exact ⟨Multiplicative.ofAdd v,congrArg j (congrArg Multiplicative.ofAdd hv)⟩
  have hact₀ (x : Y) (v : Space (K := F)) :
      j₀ (Multiplicative.ofAdd (action (β x) v))=
        x.val*j₀ (Multiplicative.ofAdd v)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (f (binaryAction (β x) v)))=_
    rw [f.isIntertwining,hact]
    rfl
  have hker : projection.toLinearMap.ker.toAddSubgroup.toSubgroup.map j₀=
      p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨Multiplicative.ofAdd (f v.toAdd),(hpf v.toAdd).trans hv,rfl⟩
    · rintro x ⟨w,hw,rfl⟩
      obtain ⟨v,hv⟩ := hf.2 w.toAdd
      refine ⟨Multiplicative.ofAdd v,?_,congrArg j (congrArg Multiplicative.ofAdd hv)⟩
      change projection v=0
      exact (hpf v).symm.trans (by rw [hv]; exact hw)
  have hfix₀ (v : Space (K := F)) : j₀ (Multiplicative.ofAdd v) ∈ centralizer (P : Set G) ↔ v.1 (.inr 0)=0 := by
    change j (Multiplicative.ofAdd (f v)) ∈ _ ↔ _
    rw [hfix,hpf]
    rfl
  have hroot := standard_root_image hF p hp j hj Y P hPY β hact hplane hpoint hfix
  simpa only [hr] using universal_root_selection hF j₀ hj₀ Y P B T hPY hTY β hact₀
    hroot hplane hfix₀ (by simpa only [hr] using hmem) (by simpa only [hr] using hne)
    (by simpa only [hr,hker] using hdis) (by simpa only [hr] using hcomp)

private theorem marked_root_selection
    (hlarge : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (hc : Nat.card p.toLinearMap.ker=Nat.card F)
    (j₀ : Multiplicative W →* G) (hj₀ : Function.Injective j₀)
    (Y : Subgroup G) (β₀ : Y →* L (K := F))
    (hact₀ : ∀ (y : Y) (w : W), j₀ (Multiplicative.ofAdd (σ (β₀ y) w)) =
      y.val*j₀ (Multiplicative.ofAdd w)*y.val⁻¹)
    (k : Sp F) (hk : ((commutator (Sp F)).subtype.comp β₀).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (P B T : Subgroup G) (hP : P ≤ Y) (hT : T ≤ Y)
    (hpoint : P=Y ⊓ centralizer (j₀.range ⊓ centralizer (P : Set G) : Set G))
    (hfix : ∀ w : W, j₀ (Multiplicative.ofAdd w) ∈ centralizer (P : Set G) ↔
      (k • p w) (.inr 0)=0)
    (hmem : ∀ b : G, b ∈ B ↔ b ∈ Y ∧ ∀ x ∈ j₀.range ⊓ centralizer (P : Set G),
      ⁅b,x⁆ ∈ ⁅P,j₀.range⁆)
    (hne : (⁅T,j₀.range ⊓ centralizer (P : Set G)⁆ ⊓ ⁅P,j₀.range⁆ : Subgroup G) ≠ ⊥)
    (hdis : Disjoint ⁅T,j₀.range ⊓ centralizer (P : Set G)⁆
      (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j₀))
    (hcomp : Disjoint ⁅T,j₀.range ⊓ centralizer (P : Set G)⁆
      ⁅j₀.range ⊓ centralizer (P : Set G),B⁆) :
    ∃ y ∈ P, (∃ u ∈ j₀.range, ⁅y,u⁆ ≠ 1) ∧
      ∀ u ∈ j₀.range, ⁅y,u⁆ ∈ ⁅T,j₀.range ⊓ centralizer (P : Set G)⁆ := by
  let kl : L (K := F) := ⟨k,by rw [LargeField.commutator_eq_top hlarge]; trivial⟩
  let β := (MulAut.conj kl).toMonoidHom.comp β₀
  let j := j₀.comp (σ kl⁻¹).toAddMonoidHom.toMultiplicative
  have hj : Function.Injective j := hj₀.comp
    (fun x y hxy => Multiplicative.toAdd.injective
      ((σ.apply_bijective kl⁻¹).1 (congrArg Multiplicative.toAdd hxy)))
  have hjr : j.range=j₀.range := by
    apply le_antisymm
    · rintro _ ⟨w,rfl⟩
      exact ⟨_,rfl⟩
    · intro u hu
      obtain ⟨w,rfl⟩ := hu
      obtain ⟨v,hv⟩ := (σ.apply_bijective kl⁻¹).2 w.toAdd
      exact ⟨Multiplicative.ofAdd v,congrArg j₀ (congrArg Multiplicative.ofAdd hv)⟩
  have hact (x : Y) (w : W) :
      j (Multiplicative.ofAdd (σ (β x) w))=x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j₀ (Multiplicative.ofAdd (σ kl⁻¹ (σ (kl*β₀ x*kl⁻¹) w)))=_
    have he : σ kl⁻¹ (σ (kl*β₀ x*kl⁻¹) w)=σ (β₀ x) (σ kl⁻¹ w) := by
      simp only [map_mul,Module.End.mul_apply,inv_self_apply]
    rw [he]
    exact hact₀ x (σ kl⁻¹ w)
  have hβ : ((commutator (Sp F)).subtype.comp β).range=planeRadicalAmbient := by
    have he : (commutator (Sp F)).subtype.comp β=
        (MulAut.conj k).toMonoidHom.comp ((commutator (Sp F)).subtype.comp β₀) := by
      ext x
      rfl
    rw [he,MonoidHom.range_comp]
    exact hk
  have hfix' (w : W) : j (Multiplicative.ofAdd w) ∈ centralizer (P : Set G) ↔
      (p w) (.inr 0)=0 := by
    change j₀ (Multiplicative.ofAdd (σ kl⁻¹ w)) ∈ _ ↔ _
    rw [hfix,p.isIntertwining]
    have he : k • binaryNatural kl⁻¹ (p w)=p w := by
      change k • (k⁻¹ • p w)=p w
      exact smul_inv_smul k (p w)
    rw [he]
  have hkernel : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j=
      p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j₀ := by
    have he (v : Multiplicative W) (hv : v ∈ p.toLinearMap.ker.toAddSubgroup.toSubgroup) :
        j v=j₀ v := by
      change j₀ (Multiplicative.ofAdd (σ kl⁻¹ v.toAdd))=j₀ v
      rw [hp.2.1 (show v.toAdd ∈ p.toLinearMap.ker from hv) kl⁻¹]
      rfl
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩; exact ⟨v,hv,(he v hv).symm⟩
    · rintro _ ⟨v,hv,rfl⟩; exact ⟨v,hv,he v hv⟩
  simpa only [hjr] using full_cover_root_selection hlarge p hp hc j hj Y P B T hP hT β hact
    hβ (by rwa [hjr]) hfix' (by simpa only [hjr] using hmem)
    (by simpa only [hjr] using hne) (by simpa only [hjr,hkernel] using hdis)
    (by simpa only [hjr] using hcomp)

end RootSelection

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem full_plane_fixed_movement_kernel_power
    {z t : Vertex d.radical}
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (hfull : Nat.card (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^n)
    (P T : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t) (hT : T ≤ Q d.radical t) :
    ∃ r : ℕ, Nat.card (⁅T,U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))⁆ ⊓
      (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
        Subgroup (FreeAmalgam d.radical))=(2^n)^r := by
  let p := MovedSection.coverProjection (replacementMovedSection h d) cv.equiv
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding=
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro v ⟨hv,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hv
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  have hFc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  have hc : Nat.card p.toLinearMap.ker=Nat.card cv.field.Carrier := by
    rw [←embedded_cover_kernel_card p cv.embedding cv.injective,hk,hfull,hFc]
  simpa only [cv.range_eq,hk,hFc] using full_cover_fixed_movement_kernel_power p cv.cover hc
    cv.embedding cv.injective P T
    (cv.actor.comp (inclusion hP)) (cv.actor.comp (inclusion hT))
    (fun x w => cv.actor_conjugation (inclusion hP x) w)
    (fun x w => cv.actor_conjugation (inclusion hT x) w)

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem movement_central_supplement
    {G : Type*} [Group G] (U C Y A : Subgroup G)
    (hCU : C ≤ normalizer (U : Set G)) (hCY : C ≤ centralizer (Y : Set G))
    (hAY : A ≤ Y) : ⁅A,U ⊔ C⁆=⁅A,U⁆ := by
  apply le_antisymm ?_ (commutator_mono le_rfl le_sup_left)
  apply commutator_le.mpr
  intro b hb x hx
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCU] at hx
  obtain ⟨u,hu,c,hc,rfl⟩ := hx
  have hbc : Commute b c := hCY hc b (hAY hb)
  rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hbc]
  simpa only [mul_one,mul_inv_cancel_right] using commutator_mem_commutator hb hu

omit [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem midpoint_centralizes_radical
    {z t : Vertex d.radical} (hz : color d.radical z=false)
    (hzt : Adjacent d.radical z t) :
    Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (hz.trans he.symm)
  rw [show Z d.radical t=omegaCenter (Q d.radical t) by simp [Z,ht,edgeOmega]]
  exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2

/-- In its own full covering field, the hyperplane movement meets the full
attachment either trivially or in the whole attachment. -/
theorem source_four_large_full_attachment_dichotomy
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hfull : Nat.card (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^n) :
    let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
    let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    A₀ ≤ ⁅X,Z d.radical a⁆ ∨ Disjoint ⁅X,Z d.radical a⁆ A₀ := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let X₀ := U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let C := Z d.radical t
  let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  let M := ⁅X,Z d.radical a⁆
  obtain ⟨⟨cv⟩,_,_,_⟩ := source_four_large_plane_cover h d g hb hsat path hat hzt c c' hcritical
  have hZaT : Z d.radical a ≤ Q d.radical t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      ((omegaCenter_le _).trans c.core_le_edge)
  have hCT : C ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    midpoint_centralizes_radical d path.end_color hzt
  have hCZ : C ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hCU : C ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCX : C ≤ normalizer (X₀ : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans
      (centralizer_le (inf_le_left.trans (U_le_Z z))))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hX : X=X₀ ⊔ C := by
    dsimp only [X,X₀]
    rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt,
      sup_comm (U d.radical z),inf_centralizer_sup_of_centralizing C (U d.radical z) P
        hCU (hCT.trans (centralizer_le hP)),sup_comm]
  have hM : M=⁅Z d.radical a,X₀⁆ := by
    rw [show M=⁅X,Z d.radical a⁆ from rfl,commutator_comm,hX]
    exact movement_central_supplement X₀ C (Q d.radical t) (Z d.radical a) hCX hCT hZaT
  obtain ⟨r,hr⟩ := full_plane_fixed_movement_kernel_power h d cv hfull P (Z d.radical a) hP hZaT
  change Nat.card (⁅Z d.radical a,X₀⁆ ⊓ A₀ : Subgroup (FreeAmalgam d.radical))=(2^n)^r at hr
  rw [←hM] at hr
  let := finite_Z d.radical z
  let : Finite A₀ := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z z))) (inclusion_injective _)
  by_cases hzero : r=0
  · right
    apply disjoint_iff.mpr
    apply Subgroup.card_eq_one.mp
    simpa only [hzero,pow_zero] using hr
  · left
    have hpos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hzero
    have hlow : 2^n ≤ (2^n)^r := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by positivity : 0 < 2^n) hpos
    have he : M ⊓ A₀=A₀ := Subgroup.eq_of_le_of_card_ge inf_le_right
      (by rw [hr,hfull]; exact hlow)
    exact he.ge.trans inf_le_left

/-- A full cover supplies an actual root element whose nontrivial displacement
lies in the hyperplane movement. The full attachment and section-centralizer
complement are the two excluded lines; the supplied plane marking is retained. -/
theorem plane_cover_hyperplane_root_element
    {z t : Vertex d.radical}
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (k : Sp cv.field.Carrier)
    (hk : ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (P B T : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t) (hT : T ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hfix : ∀ w : (replacementMovedSection h d).space.toSubmodule,
      cv.embedding (Multiplicative.ofAdd w) ∈ centralizer (P : Set (FreeAmalgam d.radical)) ↔
        (k • MovedSection.coverProjection (replacementMovedSection h d) cv.equiv w) (.inr 0)=0)
    (hmem : ∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧
      ∀ x ∈ U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),
        ⁅b,x⁆ ∈ ⁅P,U d.radical z⁆)
    (hfull : Nat.card (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^n)
    (hne : (⁅T,U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))⁆ ⊓
      ⁅P,U d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) ≠ ⊥)
    (hnot : ¬ U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ≤
      ⁅T,U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))⁆)
    (hcomp : Disjoint ⁅T,U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))⁆
      ⁅U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),B⁆) :
    ∃ y ∈ P, (∃ u ∈ U d.radical z, ⁅y,u⁆ ≠ 1) ∧
      ∀ u ∈ U d.radical z, ⁅y,u⁆ ∈ ⁅T,U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))⁆ := by
  let p := MovedSection.coverProjection (replacementMovedSection h d) cv.equiv
  let M := ⁅T,U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))⁆
  let A := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  have hkernel : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding=A := by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro v ⟨hv,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hv
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  have hFc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  have hc : Nat.card p.toLinearMap.ker=Nat.card cv.field.Carrier := by
    rw [←embedded_cover_kernel_card p cv.embedding cv.injective,hkernel,hfull,hFc]
  have hlarge : 2 < Nat.card cv.field.Carrier := by
    rw [hFc]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  obtain ⟨r,hr⟩ := full_plane_fixed_movement_kernel_power h d cv hfull P T hP hT
  have hdis : Disjoint M A := by
    apply disjoint_iff.mpr
    apply Subgroup.card_eq_one.mp
    by_cases hzero : r=0
    · simpa only [hzero,pow_zero] using hr
    · exfalso
      let := finite_Z d.radical z
      let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z z))) (inclusion_injective _)
      have hlow : 2^n ≤ (2^n)^r := by
        simpa only [pow_one] using Nat.pow_le_pow_right (by positivity : 0 < 2^n)
          (Nat.one_le_iff_ne_zero.mpr hzero)
      have he : M ⊓ A=A := Subgroup.eq_of_le_of_card_ge inf_le_right
        (by rw [hr,hfull]; exact hlow)
      exact hnot (he.ge.trans inf_le_left)
  simpa only [cv.range_eq] using marked_root_selection hlarge p cv.cover hc
    cv.embedding cv.injective (Q d.radical t) cv.actor cv.actor_conjugation k hk P B T hP hT
    (by simpa only [cv.range_eq] using hpoint) hfix
    (by simpa only [cv.range_eq] using hmem) (by simpa only [cv.range_eq] using hne)
    (by simpa only [cv.range_eq,hkernel] using hdis) (by simpa only [cv.range_eq] using hcomp)

/-- The earlier marked hyperplane geometry, with the original covering
map and complete kernel retained. This predicate contains no attachment
comparison conclusion. It provides a small application boundary for the
literal closure quotient. -/
@[expose] def HasMarkedHyperplane (z t : Vertex d.radical)
    (P B : Subgroup (FreeAmalgam d.radical)) : Prop :=
  ∃ cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t,
  ∃ k : Sp cv.field.Carrier,
    ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient ∧
    P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
    P=Q d.radical t ⊓ centralizer
      (U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
    (∀ w : (replacementMovedSection h d).space.toSubmodule,
      cv.embedding (Multiplicative.ofAdd w) ∈ centralizer (P : Set (FreeAmalgam d.radical)) ↔
        (k • MovedSection.coverProjection (replacementMovedSection h d) cv.equiv w) (.inr 0)=0) ∧
    (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧
      ∀ x ∈ U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),
        ⁅b,x⁆ ∈ ⁅P,U d.radical z⁆)

/-- The marked root selection closes the full-attachment noncontainment
subcase of the escaping comparison. The nontrivial intersection, disjoint
complement and unequal root movement are the preceding source-(4) premises. -/
theorem source_four_large_marked_attachment_le
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (P B : Subgroup (FreeAmalgam d.radical))
    (hmarked : HasMarkedHyperplane h d z t P B)
    (hi : (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n)
    (hescape : ¬ Z d.radical a ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤ Q d.radical z)
    (hfull : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^n)
    (hHcard : Nat.card (⁅Z d.radical z,P⁆ : Subgroup (FreeAmalgam d.radical))=(2^n)^2)
    (hMnot : ¬ ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ≤ ⁅Z d.radical z,P⁆)
    (hmeet : (⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ ⊓
      ⁅Z d.radical z,P⁆ : Subgroup (FreeAmalgam d.radical)) ≠ ⊥)
    (hcomp : Disjoint ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆
      ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),B⁆) :
    U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ≤
      ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a⁆ := by
  obtain ⟨cv,k,hk,hP,hB,hpoint,hfix,hmem⟩ := hmarked
  classical
  by_contra hnot
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let X₀ := U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let C := Z d.radical t
  let M := ⁅X,Z d.radical a⁆
  let Y := Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical))
  have hZaT : Z d.radical a ≤ Q d.radical t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      ((omegaCenter_le _).trans c.core_le_edge)
  have hYT : Y ≤ Q d.radical t := inf_le_left.trans hZaT
  have hCT : C ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) :=
    midpoint_centralizes_radical d path.end_color hzt
  have hCZ : C ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hCU : C ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCX : C ≤ normalizer (X₀ : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans
      (centralizer_le (inf_le_left.trans (U_le_Z z))))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hgen := Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt
  have hX : X=X₀ ⊔ C := by
    dsimp only [X,X₀]
    rw [hgen,sup_comm (U d.radical z),inf_centralizer_sup_of_centralizing C (U d.radical z) P
        hCU (hCT.trans (centralizer_le hP)),sup_comm]
  have hM : M=⁅Z d.radical a,X₀⁆ := by
    rw [show M=⁅X,Z d.radical a⁆ from rfl,commutator_comm,hX]
    exact movement_central_supplement X₀ C (Q d.radical t) (Z d.radical a) hCX hCT hZaT
  have hH : ⁅Z d.radical z,P⁆=⁅P,U d.radical z⁆ := by
    rw [commutator_comm,hgen]
    exact movement_central_supplement (U d.radical z) C (Q d.radical t) P hCU hCT hP
  have hXB : ⁅X,B⁆=⁅X₀,B⁆ := by
    rw [commutator_comm _ B,hX,movement_central_supplement X₀ C (Q d.radical t) B hCX hCT hB,commutator_comm]
  have hpointZ : P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · refine le_inf hP ?_
      rw [hX]
      apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp (hpoint.le.trans inf_le_right)) (hCT.trans (centralizer_le hP))
    · exact (inf_le_inf_left _ (centralizer_le (show X₀ ≤ X from hX ▸ le_sup_left))).trans hpoint.ge
  have hfull' := (source_four_large_attachment_card_eq h d g hb hsat path hat hzt c c' hcritical).symm.trans hfull
  obtain ⟨b,hbP,⟨u,hu,hune⟩,hval⟩ := plane_cover_hyperplane_root_element h d cv k hk P B
    (Z d.radical a) hP hZaT hpoint hfix hmem hfull'
    (by change (⁅Z d.radical a,X₀⁆ ⊓ ⁅P,U d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) ≠ ⊥
        rw [←hM,←hH]; exact hmeet)
    (by change ¬ U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ≤ ⁅Z d.radical a,X₀⁆
        rw [←hM]; exact hnot)
    (by change Disjoint ⁅Z d.radical a,X₀⁆ ⁅X₀,B⁆
        rw [←hM,←hXB]; exact hcomp)
  have hPY : P=Q d.radical z ⊔ Y :=
    (source_four_large_escaping_hyperplane h d g hb hsat path hat hzt c c'
      hcritical P hP hpointZ hi hescape).2.2.1
  have hnorm : Y ≤ normalizer (Q d.radical z : Set (FreeAmalgam d.radical)) :=
    (hYT.trans c'.edge_le).trans (Q_normalized d.radical z)
  rw [hPY,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hnorm] at hbP
  obtain ⟨q,hq,y,hy,rfl⟩ := hbP
  have hQU : Q d.radical z ≤ centralizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp ((U_le_Z z).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z path.end_color)))
  have hYUn : Y ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    (hYT.trans c'.edge_le).trans (U_normalized z)
  have he (v : FreeAmalgam d.radical) (hv : v ∈ U d.radical z) : ⁅q*y,v⁆=⁅y,v⁆ := by
    have hm : ⁅y,v⁆ ∈ U d.radical z :=
      (le_normalizer_iff_commutator_le_right.mp hYUn) (commutator_mem_commutator hy hv)
    have hh := hQU hq _ hm
    rw [commutatorElement_mul_left_eq_conj_mul,←hh,mul_inv_cancel_right,
      commutatorElement_eq_one_iff_commute.mpr (hQU hq v hv).symm,mul_one]
  have hune' : ⁅u,y⁆ ≠ 1 := by
    intro hh
    apply hune
    rw [he u hu,←commutatorElement_inv,hh,inv_one]
  have hvalues (v : FreeAmalgam d.radical) (hv : v ∈ Z d.radical z) : ⁅v,y⁆ ∈ M := by
    rw [hgen,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCU] at hv
    obtain ⟨w,hw,s,hs,rfl⟩ := hv
    have hys : Commute y s := hCT hs y (hYT hy)
    have hm : ⁅y,w⁆ ∈ M := by
      rw [←he w hw,hM]
      exact hval w hw
    have hh : ⁅y,w*s⁆ ∈ M := by
      rw [commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_commute.mpr hys]
      simpa only [mul_one,mul_inv_cancel_right] using hm
    rw [←commutatorElement_inv]
    exact M.inv_mem hh
  obtain ⟨v,hv,hvn⟩ := source_four_large_full_hyperplane_value_escape h d g hb hsat
    path hat hzt c c' hcritical P hP hpointZ hi hescape hfull hHcard hMnot y hy
      ⟨u,U_le_Z z hu,hune'⟩
  exact hvn (hvalues v hv)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
