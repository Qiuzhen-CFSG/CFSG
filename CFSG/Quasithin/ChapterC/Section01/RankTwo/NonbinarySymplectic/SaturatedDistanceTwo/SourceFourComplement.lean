module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourRadicalGeneration
public import Theory.Representation.SymplecticFourOrthogonalCover.RootOverlap
public import Theory.GroupTheory.FixedSupplementCentralizer
public import Theory.GroupTheory.NormalizedSupConsequences
/-!
# Section-centralizer factorization and complement comparison

For every supplied plane marking, the section centralizer of the full
source hyperplane has index q in the common radical. In standard shear
coordinates it is the kernel of the surjective homomorphism taking the
second diagonal entry. The proof identifies the entire pointwise fixer
with the long root and uses the full covering preimage of its displacement;
no central covering direction is discarded. Conjugation transports this
calculation through the original marking and embedding, and the midpoint
supplement gives the literal full Z-hyperplane statement.

In the escaping unequal-attachment branch, the preceding section-centralizer
comparison gives the same index q inside the opposite Z. The subgroup diamond
therefore proves T = Z′ B. Quadratic centrality and full hyperplane generation
give [Z,Z′] = [X,Z′][X,B]. The orders q cubed, q squared and q then force
[X,Z′] and [X,B] to be disjoint. Both complete fixed attachments remain in
the exported witness. The literal Chapter11 applications retain the original
quotient and action maps.

This is the complement-disjointness step of MS93 (3.7)(4), printed p.875.
Root-element selection, the remaining attachment comparisons and source
(5)/(6), and the field-four recognition remain separate source obligations.
Private cover transports adapt SourceFourHyperplane; the subgroup product
calculation adapts SourceFourFullIntersection.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(4), printed p.875.
-/

public noncomputable section
open Matrix Subgroup Representation Representation.OneCohomology Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
section Model
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


private theorem standard_section_index
    (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y P B : Subgroup G) (hPY : P ≤ Y)
    (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hY : ((commutator (Sp F)).subtype.comp β).range=planeRadicalAmbient)
    (hpoint : P=Y ⊓ centralizer (j.range ⊓ centralizer (P : Set G) : Set G))
    (hfix : ∀ w : W, j (Multiplicative.ofAdd w) ∈ centralizer (P : Set G) ↔
      (p w) (.inr 0)=0)
    (hmem : ∀ b : G, b ∈ B ↔ b ∈ Y ∧ ∀ x ∈ j.range ⊓ centralizer (P : Set G),
      ⁅b,x⁆ ∈ ⁅P,j.range⁆) : B.relIndex Y=Nat.card F := by
  let ψ := (commutator (Sp F)).subtype.comp β
  have hshear (y : Y) : ∃ C : Plane.symmetricMatrices F, Plane.shearSp C=ψ y :=
    (SymplecticConjugatePair.mem_planeRadical_iff _).mp (show ψ y ∈ planeRadicalAmbient from hY ▸ (show ψ y ∈ ψ.range from ⟨y,rfl⟩))
  have hroot : (β.comp (inclusion hPY)).range.map (commutator (Sp F)).subtype =
      RootSubgroup.group 0 := by
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
  have hmove (b : P) (w : W) : p (σ (β (inclusion hPY b)) w-w) ∈ point F := by
    have hb : (β (inclusion hPY b)).val ∈ RootSubgroup.group 0 :=
      hroot ▸ mem_map_of_mem _ (show β (inclusion hPY b) ∈
        (β.comp (inclusion hPY)).range from ⟨b,rfl⟩)
    obtain ⟨r,hr⟩ := (RootSubgroup.mem_group_iff 0 _).mp hb
    rw [map_sub,p.isIntertwining]
    change (β (inclusion hPY b)).val.val *ᵥ p w-p w ∈ point F
    rw [←hr,Roots.natural_root,add_sub_cancel_left]
    exact Submodule.mem_span_singleton.mpr ⟨_,rfl⟩
  let N := (((point F).restrictScalars (ZMod 2)).comap p.toLinearMap).toAddSubgroup.toSubgroup.map j
  have hHN : ⁅P,j.range⁆ ≤ N := by
    apply commutator_le.mpr
    rintro b hb _ ⟨w,rfl⟩
    refine ⟨Multiplicative.ofAdd (σ (β ⟨b,hPY hb⟩) w.toAdd-w.toAdd),hmove ⟨b,hb⟩ w.toAdd,?_⟩
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
    rfl
  let χ : Y →* Multiplicative F :=
    { toFun y := Multiplicative.ofAdd ((ψ y).val (.inl 1) (.inr 1))
      map_one' := by simp [ψ]
      map_mul' y z := by
        obtain ⟨C,hC⟩ := hshear y
        obtain ⟨D,hD⟩ := hshear z
        apply Multiplicative.toAdd.injective
        change (ψ (y*z)).val (.inl 1) (.inr 1)=_
        rw [map_mul,←hC,←hD]
        simp [Plane.shearSp,Matrix.fromBlocks_multiply,add_comm] }
  have hχ : Function.Surjective χ := by
    intro t
    let C : Plane.symmetricMatrices F := ⟨!![0,0;0,t.toAdd],by
      ext i k; fin_cases i <;> fin_cases k <;> rfl⟩
    have hC : Plane.shearSp C ∈ planeRadicalAmbient :=
      (SymplecticConjugatePair.mem_planeRadical_iff _).mpr ⟨C,rfl⟩
    obtain ⟨y,hy⟩ := (show Plane.shearSp C ∈ ψ.range from hY.symm ▸ hC)
    refine ⟨y,?_⟩
    change Multiplicative.ofAdd ((ψ y).val (.inl 1) (.inr 1))=t
    rw [hy]
    rfl
  have hk : B.subgroupOf Y=χ.ker := by
    ext y
    change y.val ∈ B ↔ χ y=1
    rw [hmem]
    simp only [y.property,true_and]
    obtain ⟨C,hC⟩ := hshear y
    have hval : χ y=1 ↔ C.val 1 1=0 := by
      change Multiplicative.ofAdd ((ψ y).val (.inl 1) (.inr 1))=1 ↔ _
      rw [←hC]
      rfl
    rw [hval]
    constructor
    · intro hh
      obtain ⟨w,hw⟩ := hp.1 (ClassicalOrthogonal.f 1)
      have hx : j (Multiplicative.ofAdd w) ∈ j.range ⊓ centralizer (P : Set G) :=
        ⟨⟨_,rfl⟩,(hfix w).mpr (by rw [hw]; rfl)⟩
      obtain ⟨v,hv,he⟩ := hHN (hh _ hx)
      have hvw : v=Multiplicative.ofAdd (σ (β y) w-w) := by
        apply hj
        rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
        exact he
      rw [hvw] at hv
      change p (σ (β y) w-w) ∈ point F at hv
      rw [map_sub,p.isIntertwining,hw] at hv
      have hh := (mem_point_iff _).mp hv |>.1
      change ((ψ y).val *ᵥ ClassicalOrthogonal.f 1-ClassicalOrthogonal.f 1 : Vector F) (.inl 1)=0 at hh
      simpa [←hC,Plane.shearSp,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
        Fin.sum_univ_two,Matrix.fromBlocks,ClassicalOrthogonal.f] using hh
    · intro hc x hx
      obtain ⟨w,rfl⟩ := hx.1
      have hw : (p w.toAdd) (.inr 0)=0 := (hfix w.toAdd).mp hx.2
      have hv : p (σ (β y) w.toAdd-w.toAdd) ∈ point F := by
        rw [map_sub,p.isIntertwining]
        change (ψ y).val *ᵥ p w.toAdd-p w.toAdd ∈ point F
        rw [←hC]
        apply (mem_point_iff _).mpr
        constructor
        · simp [Plane.shearSp,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
            Fin.sum_univ_two,Matrix.fromBlocks,hw,hc]
        · intro i
          fin_cases i <;> simp [Plane.shearSp,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
            Fin.sum_univ_two,Matrix.fromBlocks]
      have hh := standard_root_preimage_displacement hF p hp j Y P hPY β hact hroot
        (σ (β y) w.toAdd-w.toAdd) hv
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact] at hh
      exact hh
  change (B.subgroupOf Y).index=Nat.card F
  rw [hk,index_ker,MonoidHom.range_eq_top.mpr hχ,Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (Multiplicative F)) ≃* Multiplicative F).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

private theorem marked_section_index
    (hlarge : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j₀ : Multiplicative W →* G) (hj₀ : Function.Injective j₀)
    (Y : Subgroup G) (β₀ : Y →* L (K := F))
    (hact₀ : ∀ (y : Y) (w : W), j₀ (Multiplicative.ofAdd (σ (β₀ y) w)) =
      y.val*j₀ (Multiplicative.ofAdd w)*y.val⁻¹)
    (k : Sp F) (hk : ((commutator (Sp F)).subtype.comp β₀).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (P B : Subgroup G) (hP : P ≤ Y)
    (hpoint : P=Y ⊓ centralizer (j₀.range ⊓ centralizer (P : Set G) : Set G))
    (hfix : ∀ w : W, j₀ (Multiplicative.ofAdd w) ∈ centralizer (P : Set G) ↔
      (k • p w) (.inr 0)=0)
    (hmem : ∀ b : G, b ∈ B ↔ b ∈ Y ∧ ∀ x ∈ j₀.range ⊓ centralizer (P : Set G),
      ⁅b,x⁆ ∈ ⁅P,j₀.range⁆) :

    B.relIndex Y=Nat.card F := by
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
  exact standard_section_index hlarge p hp j hj Y P B hP β hact hβ
    (by rwa [hjr]) hfix' (by simpa only [hjr] using hmem)

end Model
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h


/-- The section centralizer of a marked full hyperplane has field index in
 the common plane radical. The original cover and arbitrary marking are retained. -/
theorem plane_cover_hyperplane_section_index
    {z t : Vertex d.radical}
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (k : Sp cv.field.Carrier)
    (hk : ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (P B : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t)
    (hpoint : P=Q d.radical t ⊓ centralizer
      (U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hfix : ∀ w : (replacementMovedSection h d).space.toSubmodule,
      cv.embedding (Multiplicative.ofAdd w) ∈ centralizer (P : Set (FreeAmalgam d.radical)) ↔
        (k • MovedSection.coverProjection (replacementMovedSection h d) cv.equiv w) (.inr 0)=0)
    (hmem : ∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧
      ∀ x ∈ U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),
        ⁅b,x⁆ ∈ ⁅P,U d.radical z⁆) : B.relIndex (Q d.radical t)=2^n := by
  have hc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  have hlarge : 2 < Nat.card cv.field.Carrier := by
    rw [hc]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  simpa only [cv.range_eq,hc] using marked_section_index hlarge
    (MovedSection.coverProjection (replacementMovedSection h d) cv.equiv) cv.cover
    cv.embedding cv.injective (Q d.radical t) cv.actor cv.actor_conjugation k hk P B hP
    (by simpa only [cv.range_eq] using hpoint) hfix (by simpa only [cv.range_eq] using hmem)

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


/-- The full source hyperplane, now with the exact section-centralizer index. -/
theorem source_four_large_hyperplane_section_index
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=2^n ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧ B.relIndex (Q d.radical t)=2^n := by
  obtain ⟨⟨cv⟩,_,_,_⟩ := source_four_large_plane_cover h d g hb hsat path hat hzt c c' hcritical
  obtain ⟨k,hk⟩ := cv.plane_image
  obtain ⟨P,B,hP,hB,hpoint,hindex,hfix,hmem,hdis,hcard,hjoin⟩ :=
    plane_cover_hyperplane_attachment h d cv k hk
  have hBi := plane_cover_hyperplane_section_index h d cv k hk P B hP hpoint hfix hmem
  let C := Z d.radical t
  let V := U d.radical z
  let X₀ := V ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let X₁ := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let Y := Q d.radical t
  have hgen : Z d.radical z=V ⊔ C :=
    Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (path.end_color.trans he.symm)
  have hC : C=omegaCenter Y := by simp [C,Y,Z,ht,edgeOmega]
  have hCY : C ≤ centralizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [hC]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hCZ : C ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  have hCU : C ≤ normalizer (V : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCX : C ≤ normalizer (X₀ : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans
      (centralizer_le (inf_le_left.trans (U_le_Z z))))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hCP : C ≤ centralizer (P : Set (FreeAmalgam d.radical)) := hCY.trans (centralizer_le hP)
  have hX : X₁=X₀ ⊔ C := by
    dsimp only [X₁,X₀]
    rw [hgen,sup_comm V C,inf_centralizer_sup_of_centralizing C V P hCU hCP,sup_comm]
  have hHZ : ⁅Z d.radical z,P⁆=⁅P,V⁆ := by
    rw [commutator_comm,hgen]
    exact movement_central_supplement V C Y P hCU hCY hP
  have hXB : ⁅X₁,B⁆=⁅X₀,B⁆ := by
    rw [commutator_comm _ B,hX,movement_central_supplement X₀ C Y B hCX hCY hB,
      commutator_comm]
  have hpointZ : P=Y ⊓ centralizer (X₁ : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · refine le_inf hP ?_
      rw [hX]
      apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp (hpoint.le.trans inf_le_right)) hCP
    · exact (inf_le_inf_left Y (centralizer_le
        (show X₀ ≤ X₁ from hX ▸ le_sup_left))).trans hpoint.ge
  have hQ : Q d.radical z ≤ P := by
    rw [hpointZ]
    apply le_inf c'.core_le_edge
    exact le_centralizer_iff.mp
      (inf_le_left.trans (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical z path.end_color)))
  have hi : X₁.relIndex (Z d.radical z)=2^n := by
    let := finite_Z d.radical z
    let : Finite X₁ := Finite.of_injective (inclusion (show X₁ ≤ Z d.radical z from inf_le_left))
      (inclusion_injective _)
    have hVX : V ⊔ X₁=Z d.radical z := by
      rw [hX,←sup_assoc,sup_eq_left.mpr (show X₀ ≤ V from inf_le_left),←hgen]
    have hXU : X₁ ≤ normalizer (V : Set (FreeAmalgam d.radical)) :=
      (inf_le_left.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
        (Subgroup.centralizer_le_normalizer _)
    rw [←hVX,relIndex_sup_of_normalizes V X₁ hXU]
    have hInf : X₁ ⊓ V=X₀ := by
      ext x
      exact ⟨fun hx => ⟨hx.2,hx.1.2⟩,fun hx => ⟨⟨U_le_Z z hx.1,hx.2⟩,hx.1⟩⟩
    rw [←inf_relIndex_right,hInf,inf_relIndex_left]
    exact hindex
  have hCX₁ : C ≤ X₁ := le_inf hCZ hCP
  have hZaQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hcommon : ⁅Z d.radical a,Z d.radical z⁆ ≤ C := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hZaQ).trans
      (source_two_midpoint_containment h d g hb hsat path hat hzt c c')
  refine ⟨P,B,hQ,hP,hB,hpointZ,hi,hCX₁,hcommon.trans hCX₁,?_,?_,?_,?_,?_,hBi⟩
  · intro b
    rw [hmem]
    constructor
    · rintro ⟨hb,hm⟩
      refine ⟨hb,fun x hx => ?_⟩
      change x ∈ X₁ at hx
      rw [hX,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCX] at hx
      obtain ⟨u,hu,v,hv,rfl⟩ := hx
      have hbv : Commute b v := hCY hv b hb
      rw [hHZ,commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_commute.mpr hbv]
      simpa only [mul_one,mul_inv_cancel_right] using hm u hu
    · rintro ⟨hb,hm⟩
      refine ⟨hb,fun x hx => ?_⟩
      rw [←hHZ]
      apply hm x
      change x ∈ X₁
      rw [hX]
      exact mem_sup_left hx
  · rw [hXB]
    exact hdis
  · rw [hXB]
    exact hcard
  · rw [hHZ,hXB]
    exact hjoin
  · rw [commutator_comm]
    exact (commutator_mono hP le_rfl).trans_eq
      (source_four_large_full_movement h d g hb hsat path hat hzt c c' hcritical)

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem subgroup_product_card {G : Type*} [Group G]
    (B C : Subgroup G) (hn : C ≤ normalizer (B : Set G)) :
    Nat.card B * Nat.card C = Nat.card (B ⊓ C : Subgroup G) * Nat.card (B ⊔ C : Subgroup G) := by
  let V := B ⊔ C
  let _ : (B.subgroupOf V).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  have hindex := relIndex_sup_left (C.subgroupOf V) (B.subgroupOf V)
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf le_rfl,relIndex_subgroupOf le_sup_right] at hindex
  have hindex' : B.relIndex V = (B ⊓ C).relIndex C :=
    hindex.trans (inf_relIndex_right B C).symm
  have hcardV := relIndex_mul_relIndex (⊥ : Subgroup G) B V bot_le le_sup_left
  have hcardC := relIndex_mul_relIndex (⊥ : Subgroup G) (B ⊓ C) C bot_le inf_le_right
  simp only [relIndex_bot_left] at hcardV hcardC
  rw [hindex'] at hcardV
  rw [←hcardC,←hcardV]
  ac_rfl

/-- In the escaping unequal-attachment branch the section centralizer
supplements the opposite Z in the whole radical. Its hyperplane movement
is disjoint from the opposite movement, and together they give the full
common displacement. -/
theorem source_four_large_unequal_complement
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ P B : Subgroup (FreeAmalgam d.radical),
      let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
      let H₀ := ⁅Z d.radical z,P⁆
      let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
      let A₁ := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
      Q d.radical z ≤ P ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      P=Q d.radical t ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ∧
      X.relIndex (Z d.radical z)=2^n ∧
      Z d.radical t ≤ X ∧ ⁅Z d.radical a,Z d.radical z⁆ ≤ X ∧
      (∀ b : FreeAmalgam d.radical, b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam d.radical))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧
      B.relIndex (Q d.radical t)=2^n ∧
      (¬ Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) ≤ Q d.radical z →
        Nat.card A₁=2^n ∧ Nat.card A₀=2^n ∧
        Q d.radical t=Z d.radical a ⊔ B ∧
        ⁅Z d.radical a,Z d.radical z⁆=⁅X,Z d.radical a⁆ ⊔ ⁅X,B⁆ ∧
        Disjoint ⁅X,Z d.radical a⁆ ⁅X,B⁆) := by
  obtain ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi⟩ :=
    source_four_large_hyperplane_section_index h d g hb hsat path hat hzt c c' hcritical
  refine ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi,?_⟩
  intro hescape
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let D := ⁅Z d.radical a,Z d.radical z⁆
  let M := ⁅X,Z d.radical a⁆
  let A := ⁅X,B⁆
  have hfull : Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical))=2^n := by
    by_contra hn
    exact hne (source_four_large_escaping_small_attachment_eq h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape hn)
  have hfull' := (source_four_large_attachment_card_eq h d g hb hsat path hat hzt c c' hcritical).symm.trans hfull
  have hn := source_four_large_escaping_not_le_hyperplane h d g hb hsat path hat hzt c c'
    hcritical P B hP hpoint hi hmem hcard hne hescape
  have hZaT : Z d.radical a ≤ Q d.radical t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      ((omegaCenter_le _).trans c.core_le_edge)
  have he : Z d.radical a ⊓ B=Z d.radical a ⊓ centralizer (X : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro u ⟨hu,hbB⟩
      refine ⟨hu,?_⟩
      apply (source_four_large_full_section_centralizer h d g hb hsat path hat hzt c c'
        hcritical P hP hpoint hi hescape hfull hn u hu).mp
      intro x hx
      rw [←commutatorElement_inv]
      exact inv_mem (((hmem u).mp hbB).2 x hx)
    · rintro u ⟨hu,hc⟩
      refine ⟨hu,(hmem u).mpr ⟨hZaT hu,?_⟩⟩
      intro x hx
      rw [commutatorElement_eq_one_iff_commute.mpr (hc x hx).symm]
      exact one_mem _
  have hBZ : B.relIndex (Z d.radical a)=2^n := by
    rw [←inf_relIndex_left,he]
    exact (source_four_large_escaping_hyperplane h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape).1
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion c'.edge_le) (inclusion_injective _)
  let : Finite B := Finite.of_injective (inclusion hB) (inclusion_injective _)
  have hnorm : B ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    hB.trans (c.edge_le.trans (Z_normalized d.radical a))
  have hJ : Z d.radical a ⊔ B ≤ Q d.radical t := sup_le hZaT hB
  have hfactor : Q d.radical t=Z d.radical a ⊔ B := by
    have hh := relIndex_mul_relIndex B (Z d.radical a ⊔ B) (Q d.radical t) le_sup_right hJ
    rw [relIndex_sup_of_normalizes _ _ hnorm,hBZ,hBi] at hh
    have hidx : (Z d.radical a ⊔ B).relIndex (Q d.radical t)=1 := by
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^n) (hh.trans (mul_one _).symm)
    exact le_antisymm (relIndex_eq_one.mp hidx) hJ
  have hXD : ⁅X,Q d.radical t⁆=D :=
    source_four_large_hyperplane_full_movement h d g hb hsat path hat hzt c c' hcritical P hP hi
  have hMD : M ≤ D := (commutator_mono le_rfl hZaT).trans_eq hXD
  have hAD : A ≤ D := (commutator_mono le_rfl hB).trans_eq hXD
  have hDC : D ≤ Z d.radical t := by
    change ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical t
    rw [commutator_comm]
    exact (commutator_mono le_rfl ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _))).trans (source_two_midpoint_containment h d g hb hsat path hat hzt c c')
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro hh
    exact adjacent_color_ne d.radical hzt (path.end_color.trans hh.symm)
  have hDT : D ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    apply hDC.trans
    rw [show Z d.radical t=omegaCenter (Q d.radical t) by simp [Z,ht,edgeOmega]]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hsup : D=M ⊔ A := by
    apply le_antisymm ?_ (sup_le hMD hAD)
    rw [←hXD]
    apply commutator_le.mpr
    intro x hx b hbT
    rw [hfactor,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hnorm] at hbT
    obtain ⟨u,hu,v,hv,rfl⟩ := hbT
    have hxv : ⁅x,v⁆ ∈ A := commutator_mem_commutator hx hv
    have hh := hDT (hAD hxv) u (hZaT hu)
    rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc ⁅x,u⁆ u ⁅x,v⁆,hh,
      ←mul_assoc ⁅x,u⁆ ⁅x,v⁆ u,mul_inv_cancel_right]
    exact (M ⊔ A).mul_mem (mem_sup_left (commutator_mem_commutator hx hu)) (mem_sup_right hxv)
  have hMc : Nat.card M=(2^n)^2 := by
    have hh := (source_four_large_escaping_movement h d g hb hsat path hat hzt c c'
      hcritical P hP hpoint hi hescape).2.2
    simpa only [hfull,pow_two] using hh
  have hDc : Nat.card D=(2^n)^3 := by
    rw [(source_four_large_displacement_order h d g hb hsat path hat hzt c c' hcritical).2.2,hfull']
    exact (pow_succ (2^n) 2).symm
  have hDA : Disjoint M A := by
    have hDZ : D ≤ Z d.radical z := hDC.trans (Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt)
    let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
    have hAM : A ≤ normalizer (M : Set (FreeAmalgam d.radical)) :=
      (hAD.trans hDZ).trans ((Z d.radical z).le_centralizer.trans (centralizer_le (hMD.trans hDZ)))
        |>.trans (Subgroup.centralizer_le_normalizer _)
    have hh := subgroup_product_card M A hAM
    rw [hMc,hcard,←hsup,hDc,←pow_succ] at hh
    apply disjoint_iff.mpr
    apply Subgroup.card_eq_one.mp
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2^n)^3)
    simpa only [one_mul] using hh.symm
  exact ⟨hfull,hfull',hfactor,hsup,hDA⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
