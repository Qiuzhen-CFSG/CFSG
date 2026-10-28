module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourMarkedComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourEquality

/-!
# Full fixed-attachment equality in MS93 (3.7)(4)

The escaping-centralizer comparison applies to every marked hyperplane.
Consequently no subgroup of the opposite critical image has displacement
dimension one: its fixed hyperplane would have an escaping centralizer.
The image has order q squared. Evaluation at every nonzero lower direction
is therefore a bijection onto the natural plane; equal evaluations would
give a nonidentity quotient with a fixed hyperplane.

This supplies the omitted operation argument on printed p.875. For a
nonzero plane vector u and any central coordinate t, choose a nonzero
lower direction w with w dot u = t squared, then the actual opposite
actor taking w to u. The orthogonal-cover correction formula gives the
individual displacement (u,t). Transport through the original universal
cover quotient retains its entire binary central kernel and the original
conjugation maps. Thus every element of the common displacement outside
one full attachment is an individual commutator of the two Z-layers.
An individual commutator in the other attachment is trivial. Containment
and the previously proved equality of attachment orders identify them.

Combining this large-image argument with the existing field-sized case
proves (4) for every critical pair, at the original field degree. This
does not assert source (5)/(6), degree two, or the block conclusion.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(4), printed p.875, especially its final operation argument.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Matrix Subgroup Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
private def topVector (u : Fin 2 → F) : Theory.SpecificGroups.SymplecticFour.Vector F := Sum.elim u 0

omit [Finite F] [CharP F 2] in
private theorem shear_displacement (B : Plane.symmetricMatrices F) (v : Theory.SpecificGroups.SymplecticFour.Vector F) :
    (Plane.shearSp B) • v-v=topVector (B.val *ᵥ (fun i => v (.inr i))) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Plane.shearSp,topVector,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks]

private theorem shear_correction_square (B : Plane.symmetricMatrices F) (v : Theory.SpecificGroups.SymplecticFour.Vector F) :
    correction (Plane.shearSp B) v ^ 2 =
      dotProduct (fun i => v (.inr i)) (B.val *ᵥ (fun i => v (.inr i))) := by
  have h := correction_square (Plane.shearSp B) v
  have he := shear_displacement B v
  have hv := sub_eq_iff_eq_add.mp he
  change (Plane.shearSp B).val *ᵥ v=topVector (B.val *ᵥ (fun i => v (.inr i)))+v at hv
  rw [hv] at h
  simp only [rowQuadratic,Pi.add_apply,topVector,Sum.elim_inl,Sum.elim_inr,
    Pi.zero_apply,zero_add] at h
  dsimp only [dotProduct]
  rw [Fin.sum_univ_two]
  linear_combination -h

omit [Finite F] [CharP F 2] in
private theorem plane_cyclic_rank_one
    (a : Sp F) (ha : a ∈ planeRadicalAmbient) (hne : a ≠ 1)
    (v : Theory.SpecificGroups.SymplecticFour.Vector F) (hv : v ∉ plane F) (hfix : a • v=v) :
    Module.finrank F (displacementSpace (zpowers a))=1 := by
  let D := displacementSpace (zpowers a)
  let X := TwoLocalCover.fixedSpace (zpowers a)
  have fixed (u : Theory.SpecificGroups.SymplecticFour.Vector F) (hu : a • u=u) : u ∈ X := by
    have hh : zpowers a ≤ MulAction.stabilizer (Sp F) u := zpowers_le.mpr hu
    exact fun b hb => hh hb
  have hPX : plane F ≤ X := by
    intro u hu
    apply fixed u
    obtain ⟨B,rfl⟩ := (SymplecticConjugatePair.mem_planeRadical_iff a).mp ha
    apply sub_eq_zero.mp
    rw [shear_displacement]
    have he : (fun i => u (.inr i))=0 := funext hu
    rw [he,Matrix.mulVec_zero]
    ext i
    cases i <;> rfl
  have hlt : plane F < X := lt_of_le_of_ne hPX (fun he => hv (he ▸ fixed v hfix))
  have hdX := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_plane] at hdX
  have hp := LinearMap.BilinForm.finrank_orthogonal
    (W := D) TwoLocalCover.form_nondegenerate
  rw [orthogonal_displacementSpace] at hp
  have hV : Module.finrank F (Theory.SpecificGroups.SymplecticFour.Vector F)=4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
  rw [hV] at hp
  have hdle := D.finrank_le
  rw [hV] at hdle
  have hdpos : 0<Module.finrank F D := by
    by_contra hn
    have hd0 : Module.finrank F D=0 := by omega
    have hDb : D=⊥ := Submodule.finrank_eq_zero.mp hd0
    have he (w : Theory.SpecificGroups.SymplecticFour.Vector F) : a • w=w := by
      apply sub_eq_zero.mp
      have hh := Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp (zpowers a).subtype)
        ⟨a,mem_zpowers a⟩ w
      change a • w-w ∈ D at hh
      rw [hDb] at hh
      exact hh
    apply hne
    apply Subtype.ext
    ext i j
    have hh := congrFun (he (Pi.single j 1)) i
    simpa [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Matrix.mulVec_single,Matrix.one_apply,Pi.single_apply] using hh
  change Module.finrank F X=4-Module.finrank F D at hp
  change Module.finrank F D=1
  omega

omit [CharP F 2] in
private theorem plane_evaluation_bijective
    (J : Subgroup (Sp F)) (hJ : J ≤ planeRadicalAmbient)
    (hc : Nat.card J=Nat.card F^2)
    (hn : ∀ a ∈ J, Module.finrank F (displacementSpace (zpowers a)) ≠ 1)
    (w : Fin 2 → F) (hw : w ≠ 0) :
    Function.Bijective (fun a : J => fun i : Fin 2 =>
      (a.val • (Sum.elim 0 w : Theory.SpecificGroups.SymplecticFour.Vector F)) (.inl i)) := by
  let v : Theory.SpecificGroups.SymplecticFour.Vector F := Sum.elim 0 w
  let f := fun a : J => fun i : Fin 2 => (a.val • v) (.inl i)
  have hv : v ∉ plane F := by intro hv; exact hw (funext hv)
  have hi : Function.Injective f := by
    intro a b hab
    have he : a.val • v=b.val • v := by
      ext i
      rcases i with i | i
      · exact congrFun hab i
      · obtain ⟨A,hA⟩ := (SymplecticConjugatePair.mem_planeRadical_iff a.val).mp (hJ a.property)
        obtain ⟨B,hB⟩ := (SymplecticConjugatePair.mem_planeRadical_iff b.val).mp (hJ b.property)
        have h1 := congrFun (shear_displacement A v) (.inr i)
        have h2 := congrFun (shear_displacement B v) (.inr i)
        rw [hA] at h1
        rw [hB] at h2
        change (a.val • v) (.inr i)-v (.inr i)=0 at h1
        change (b.val • v) (.inr i)-v (.inr i)=0 at h2
        exact (sub_eq_zero.mp h1).trans (sub_eq_zero.mp h2).symm
    have hmem : b.val⁻¹*a.val ∈ J := J.mul_mem (J.inv_mem b.property) a.property
    have hfix : (b.val⁻¹*a.val) • v=v := by rw [mul_smul,he,inv_smul_smul]
    have hz : b.val⁻¹*a.val=1 := by
      by_contra hne
      exact hn _ hmem (plane_cyclic_rank_one _ (hJ hmem) hne v hv hfix)
    exact Subtype.ext ((inv_mul_eq_one.mp hz).symm)
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨hi,?_⟩
  rw [hc,Nat.card_fun,Nat.card_fin]

omit [Finite F] [CharP F 2] in
private theorem nonzero_pairing_fiber
    (u : Fin 2 → F) (hu : u ≠ 0) (t : F) :
    ∃ w : Fin 2 → F, w ≠ 0 ∧ dotProduct w u=t := by
  by_cases ht : t=0
  · refine ⟨![u 1,-u 0],?_,?_⟩
    · intro he
      apply hu
      have h0 := congrFun he 0
      have h1 := congrFun he 1
      ext i
      fin_cases i <;> simp_all
    · simp [dotProduct,Fin.sum_univ_two,ht,mul_comm]
  · obtain ⟨i,hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra hn
      exact hu (funext (fun i => not_ne_iff.mp (not_exists.mp hn i)))
    refine ⟨Pi.single i (t/u i),?_,?_⟩
    · intro he
      have hh := congrFun he i
      simp only [Pi.single_eq_same,Pi.zero_apply] at hh
      exact ht ((div_eq_zero_iff).mp hh |>.resolve_right hi)
    · rw [single_dotProduct]
      exact div_mul_cancel₀ _ hi

private theorem plane_individual_values
    (J : Subgroup (Sp F)) (hJ : J ≤ planeRadicalAmbient)
    (hc : Nat.card J=Nat.card F^2)
    (hn : ∀ a ∈ J, Module.finrank F (displacementSpace (zpowers a)) ≠ 1)
    (u : Fin 2 → F) (hu : u ≠ 0) (t : F) :
    ∃ a ∈ J, ∃ v : Space (K := F),
      fullAction a v-v=(topVector u,t) := by
  obtain ⟨w,hw,hwu⟩ := nonzero_pairing_fiber u hu (t^2)
  obtain ⟨a,ha⟩ := (plane_evaluation_bijective J hJ hc hn w hw).2 u
  obtain ⟨B,hB⟩ := (SymplecticConjugatePair.mem_planeRadical_iff a.val).mp (hJ a.property)
  let v : Theory.SpecificGroups.SymplecticFour.Vector F := Sum.elim 0 w
  have hBu : B.val *ᵥ w=u := by
    ext i
    have hh := congrFun (shear_displacement B v) (.inl i)
    rw [hB] at hh
    have hh' := congrFun ha i
    change (a.val • v) (.inl i)=u i at hh'
    change (a.val • v) (.inl i)-0=(B.val *ᵥ w) i at hh
    simpa only [sub_zero,hh'] using hh.symm
  refine ⟨a.val,a.property,(v,0),?_⟩
  apply Prod.ext
  · change a.val • v-v=topVector u
    rw [←hB,shear_displacement]
    exact congrArg topVector hBu
  · simp only [fullAction_apply,Prod.snd_sub,sub_zero,zero_add]
    apply CharTwo.sq_injective
    dsimp only
    rw [←hB,shear_correction_square]
    change dotProduct w (B.val *ᵥ w)=t^2
    rw [hBu,hwu]

private theorem embedded_plane_values
    [Algebra (ZMod 2) F] {W G : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (A : Subgroup G) (β : A →* L (K := F))
    (hact : ∀ a : A, ∀ w : W, j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hJ : ((commutator (Sp F)).subtype.comp β).range ≤ planeRadicalAmbient)
    (hc : Nat.card ((commutator (Sp F)).subtype.comp β).range=Nat.card F^2)
    (hn : ∀ a ∈ ((commutator (Sp F)).subtype.comp β).range,
      Module.finrank F (displacementSpace (zpowers a)) ≠ 1)
    (b : G) (hb : b ∈ ⁅A,j.range⁆)
    (hbK : b ∉ p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) :
    ∃ a ∈ A, ∃ w : W, ⁅a,j (Multiplicative.ofAdd w)⁆=b := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  let jf := j.comp f.toAddMonoidHom.toMultiplicative
  let D : AddSubgroup (Space (K := F)) :=
    (plane F).toAddSubgroup.comap (LinearMap.fst F (Natural (K := F)) F).toAddMonoidHom
  have hD : ⁅A,j.range⁆ ≤ D.toSubgroup.map jf := by
    apply commutator_le.mpr
    intro a ha w hw
    obtain ⟨w,rfl⟩ := hw
    obtain ⟨v,hv⟩ := hf w.toAdd
    let u := binaryAction (β ⟨a,ha⟩) v-v
    refine ⟨Multiplicative.ofAdd u,?_,?_⟩
    · change u.1 ∈ plane F
      obtain ⟨B,hB⟩ := (SymplecticConjugatePair.mem_planeRadical_iff _).mp
        (hJ (show (β ⟨a,ha⟩).val ∈ ((commutator (Sp F)).subtype.comp β).range from ⟨_,rfl⟩))
      change (β ⟨a,ha⟩).val • v.1-v.1 ∈ plane F
      rw [←hB,shear_displacement]
      exact fun _ => rfl
    · change j (Multiplicative.ofAdd (f (binaryAction (β ⟨a,ha⟩) v-v)))=⁅a,j w⁆
      rw [map_sub,f.isIntertwining,hv,ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
  obtain ⟨v,hv,hvb⟩ := hD hb
  have hvP : v.toAdd.1 ∈ plane F := hv
  let u : Fin 2 → F := fun i => v.toAdd.1 (.inl i)
  have hu : topVector u=v.toAdd.1 := by
    ext i
    rcases i with i | i
    · rfl
    · exact (hvP i).symm
  have hu0 : u ≠ 0 := by
    intro he
    apply hbK
    refine ⟨Multiplicative.ofAdd (f v.toAdd),?_,hvb⟩
    change p (f v.toAdd)=0
    rw [hpf]
    change v.toAdd.1=0
    rw [←hu,he]
    ext i
    cases i <;> rfl
  obtain ⟨a,ha,w,hw⟩ := plane_individual_values _ hJ hc hn u hu0 v.toAdd.2
  obtain ⟨x,hx⟩ := ha
  have hh : binaryAction (β x) w-w=v.toAdd := by
    change fullAction ((β x).val) w-w=v.toAdd
    change (β x).val=a at hx
    rw [hx,hw,hu]
  refine ⟨x.val,x.property,f w,?_⟩
  have he := congrArg (fun w => j (Multiplicative.ofAdd (f w))) hh
  rw [map_sub,f.isIntertwining,ofAdd_sub,map_div,div_eq_mul_inv,hact] at he
  exact he.trans hvb


private theorem marked_embedded_plane_values
    [Algebra (ZMod 2) F] {W G : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (hF : 2 < Nat.card F)
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j₀ : Multiplicative W →* G) (A : Subgroup G) (β₀ : A →* L (K := F))
    (hact₀ : ∀ a : A, ∀ w : W, j₀ (Multiplicative.ofAdd (σ (β₀ a) w))=
      a.val*j₀ (Multiplicative.ofAdd w)*a.val⁻¹)
    (k : Sp F)
    (hJ : (((commutator (Sp F)).subtype.comp β₀).range.map (MulAut.conj k).toMonoidHom) ≤ planeRadicalAmbient)
    (hc : Nat.card ((commutator (Sp F)).subtype.comp β₀).range=Nat.card F^2)
    (hn : ∀ a ∈ ((commutator (Sp F)).subtype.comp β₀).range,
      Module.finrank F (displacementSpace (zpowers a)) ≠ 1)
    (b : G) (hb : b ∈ ⁅A,j₀.range⁆)
    (hbK : b ∉ p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j₀) :
    ∃ a ∈ A, ∃ w : W, ⁅a,j₀ (Multiplicative.ofAdd w)⁆=b := by
  let kl : L (K := F) := ⟨k,by rw [LargeField.commutator_eq_top hF]; trivial⟩
  let β := (MulAut.conj kl).toMonoidHom.comp β₀
  let j := j₀.comp (σ kl⁻¹).toAddMonoidHom.toMultiplicative
  have hjr : j.range=j₀.range := by
    apply le_antisymm
    · rintro _ ⟨w,rfl⟩
      exact ⟨_,rfl⟩
    · rintro _ ⟨w,rfl⟩
      obtain ⟨v,hv⟩ := (σ.apply_bijective kl⁻¹).2 w.toAdd
      exact ⟨Multiplicative.ofAdd v,congrArg j₀ (congrArg Multiplicative.ofAdd hv)⟩
  have hact (x : A) (w : W) :
      j (Multiplicative.ofAdd (σ (β x) w))=x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j₀ (Multiplicative.ofAdd (σ kl⁻¹ (σ (kl*β₀ x*kl⁻¹) w)))=_
    have he : σ kl⁻¹ (σ (kl*β₀ x*kl⁻¹) w)=σ (β₀ x) (σ kl⁻¹ w) := by
      simp only [map_mul,Module.End.mul_apply,inv_self_apply]
    rw [he]
    exact hact₀ x (σ kl⁻¹ w)
  have he : (commutator (Sp F)).subtype.comp β=
      (MulAut.conj k).toMonoidHom.comp ((commutator (Sp F)).subtype.comp β₀) := by ext; rfl
  have hr : ((commutator (Sp F)).subtype.comp β).range=
      ((commutator (Sp F)).subtype.comp β₀).range.map (MulAut.conj k).toMonoidHom := by
    rw [he,MonoidHom.range_comp]
  have hcard : Nat.card ((commutator (Sp F)).subtype.comp β).range=Nat.card F^2 := by
    rw [hr,card_map_of_injective (MulAut.conj k).injective,hc]
  have hno : ∀ a ∈ ((commutator (Sp F)).subtype.comp β).range,
      Module.finrank F (displacementSpace (zpowers a)) ≠ 1 := by
    rw [hr]
    rintro a ⟨a,ha,rfl⟩
    rw [←MonoidHom.map_zpowers,PointRadicalAction.displacement_conjugate,(toLinear k).finrank_map_eq]
    exact hn a ha
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j ≤
      p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j₀ := by
    rintro b ⟨w,hw,rfl⟩
    refine ⟨Multiplicative.ofAdd (σ kl⁻¹ w.toAdd),?_,rfl⟩
    change p (σ kl⁻¹ w.toAdd)=0
    rw [p.isIntertwining,show p w.toAdd=0 from hw,map_zero]
  obtain ⟨a,ha,w,hw⟩ := embedded_plane_values p hp j A β hact (hr ▸ hJ) hcard hno b
    (hjr ▸ hb) (fun hmem => hbK (hk hmem))
  exact ⟨a,ha,σ kl⁻¹ w,hw⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
private theorem displacement_eq_bot_of_image_one
    {E J : Type*} [Field E] [Group J] (α : J →* Sp E)
    (hα : ∀ x, α x=1) : displacementSpace α.range=⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨x,w⟩,rfl⟩
  obtain ⟨b,hb⟩ := x.property
  change x.val • w-w ∈ (⊥ : Submodule E (Theory.SpecificGroups.SymplecticFour.Vector E))
  rw [←hb,hα,one_smul,sub_self]
  exact Submodule.zero_mem _

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Every subgroup of the opposite critical image avoids rank-one displacement
when the complete attachments differ; its hypothetical fixed hyperplane
would contradict the proved nonescaping centralizer comparison. -/
theorem source_four_large_no_rank_one_subactor
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (A : Subgroup (FreeAmalgam d.radical)) (hAZ : A ≤ Z d.radical a)
    (hAT : A ≤ Q d.radical t) :
    Module.finrank cv.field.Carrier (displacementSpace
      (((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hAT)).range) ≠ 1 := by
  intro hd
  have hi := plane_cover_full_fixed_index h d g hb path.end_color hzt cv A hAT
  rw [hd,pow_one] at hi
  obtain ⟨P,B,hm,hP,hpoint,hX⟩ :=
    plane_cover_dual_marked_hyperplane h d g hb path.end_color hzt cv A hAT hi
  have hn := source_four_large_marked_centralizer_le h d g hb hsat path hat hzt c c'
    hcritical hne P B hm
  have hAQ : A ≤ Q d.radical z := by
    intro x hx
    apply hn
    refine ⟨hAZ hx,?_⟩
    intro u hu
    have hu' : u ∈ Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) := hu
    exact ((hX.le hu').2 x hx).symm
  let α := ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hAT)
  have hz : displacementSpace α.range=⊥ := displacement_eq_bot_of_image_one α (fun b => by
    change inclusion hAT b ∈ ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).ker
    rw [cv.actor_kernel]
    exact hAQ b.property)
  change Module.finrank cv.field.Carrier (displacementSpace α.range)=1 at hd
  rw [hz,finrank_bot] at hd
  omega

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem cyclic_image
    {G J : Type*} [Group G] [Group J] (T : Subgroup G) (α : T →* J)
    (y : G) (hy : y ∈ T) :
    (α.comp (inclusion (zpowers_le.mpr hy))).range=zpowers (α ⟨y,hy⟩) := by
  apply le_antisymm
  · rintro b ⟨a,rfl⟩
    obtain ⟨m,hm⟩ := mem_zpowers_iff.mp a.property
    apply mem_zpowers_iff.mpr
    refine ⟨m,?_⟩
    change (α ⟨y,hy⟩)^m=α (inclusion (zpowers_le.mpr hy) a)
    rw [←map_zpow]
    congr 1
    exact Subtype.ext hm
  · apply zpowers_le.mpr
    exact ⟨⟨y,mem_zpowers y⟩,rfl⟩


private theorem large_actor_geometry
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (hZaT : Z d.radical a ≤ Q d.radical t) :
    let γ := ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hZaT)
    Nat.card γ.range=Nat.card cv.field.Carrier^2 ∧
      ∀ x ∈ γ.range, Module.finrank cv.field.Carrier (displacementSpace (zpowers x)) ≠ 1 := by
  let α := (commutator (Sp cv.field.Carrier)).subtype.comp cv.actor
  let γ := α.comp (inclusion hZaT)
  have hc : Nat.card γ.range=Nat.card cv.field.Carrier^2 := by
    have hidx := (source_four_large_midpoint_kernels h d g hb hsat path hat hzt c c' hcritical).2.2.1
    have hcard : Nat.card γ.range=(Q d.radical z).relIndex (Z d.radical a) := by
      dsimp only [γ,α]
      rw [←index_ker,←MonoidHom.comap_ker,cv.actor_kernel,comap_inclusion_subgroupOf]
      rfl
    rw [hcard,hidx,cv.field.card_eq,cv.degree]
  have hn : ∀ x ∈ γ.range,
      Module.finrank cv.field.Carrier (displacementSpace (zpowers x)) ≠ 1 := by
    rintro x ⟨y,rfl⟩
    have hcy := cyclic_image (Q d.radical t) α y.val (hZaT y.property)
    have hno := source_four_large_no_rank_one_subactor h d g hb hsat path hat hzt c c'
      hcritical hne cv (zpowers y.val) (zpowers_le.mpr y.property) (zpowers_le.mpr (hZaT y.property))
    intro he
    apply hno
    exact (congrArg (fun J : Subgroup (Sp cv.field.Carrier) =>
      Module.finrank cv.field.Carrier (displacementSpace J)) hcy).trans he
  exact ⟨hc,hn⟩

/-- In the large unequal-attachment branch, every element of the common
displacement outside the second complete attachment is an individual
commutator of the original full Z-layers. -/
theorem source_four_large_unequal_values
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hne : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≠
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (b : FreeAmalgam d.radical) (hbR : b ∈ ⁅Z d.radical a,Z d.radical z⁆)
    (hbA : b ∉ U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) :
    ∃ x ∈ Z d.radical a, ∃ y ∈ Z d.radical z, ⁅x,y⁆=b := by
  obtain ⟨⟨cv⟩,_⟩ := source_four_large_plane_cover h d g hb hsat path hat hzt c c' hcritical
  have hZaT : Z d.radical a ≤ Q d.radical t :=
    ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)).trans c.core_le_edge
  let α := (commutator (Sp cv.field.Carrier)).subtype.comp cv.actor
  let β := cv.actor.comp (inclusion hZaT)
  let γ := α.comp (inclusion hZaT)
  obtain ⟨k,hk⟩ := cv.plane_image
  have hJ : γ.range.map (MulAut.conj k).toMonoidHom ≤ planeRadicalAmbient := by
    have hle : γ.range ≤ α.range := by
      rintro _ ⟨x,rfl⟩
      exact ⟨inclusion hZaT x,rfl⟩
    exact (map_mono hle).trans_eq hk
  obtain ⟨hc,hn⟩ := large_actor_geometry h d g hb hsat path hat hzt c c' hcritical hne cv hZaT
  let p := MovedSection.coverProjection (replacementMovedSection h d) cv.equiv
  have hker : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding=
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro x ⟨hx,hxC⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact ⟨w,(cv.kernel _).mpr hxC,rfl⟩
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  have hCz := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  have hCa := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
  have hCU : Z d.radical t ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    (hCz.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hmove : ⁅Z d.radical a,Z d.radical z⁆ ≤ ⁅Z d.radical a,U d.radical z⁆ := by
    apply commutator_le.mpr
    intro x hx y hy
    rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt,
      ←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCU] at hy
    obtain ⟨u,hu,v,hv,rfl⟩ := hy
    have hcomm : Commute x v := (Z d.radical a).le_centralizer (hCa hv) x hx
    rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hcomm]
    simpa only [mul_one,mul_inv_cancel_right] using commutator_mem_commutator hx hu
  have hF : 2 < Nat.card cv.field.Carrier := by
    rw [cv.field.card_eq,cv.degree]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  obtain ⟨x,hx,w,hw⟩ := marked_embedded_plane_values hF p cv.cover cv.embedding
    (Z d.radical a) β (fun x w => cv.actor_conjugation (inclusion hZaT x) w) k hJ hc hn b
    (by rw [cv.range_eq]; exact hmove hbR) (by rwa [hker])
  exact ⟨x,hx,cv.embedding (Multiplicative.ofAdd w),U_le_Z z (cv.range_eq ▸ ⟨_,rfl⟩),hw⟩

/-- The nonescaping comparison completes source (4) at critical index q squared. -/
theorem source_four_large_fixed_attachments
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
  classical
  by_contra hne
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let B := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  have hAB : A ≤ B := by
    intro b hbA
    by_contra hbB
    have hgeom := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
    have hbR : b ∈ ⁅Z d.radical a,Z d.radical z⁆ := hgeom.2.2.2.2.2.2 (mem_sup_left hbA)
    obtain ⟨x,hx,y,hy,he⟩ := source_four_large_unequal_values h d g hb hsat path hat hzt c c' hcritical hne b hbR hbB
    have heinv : ⁅y,x⁆=b⁻¹ := by rw [←commutatorElement_inv,he]
    have hone := critical_full_value_in_fixed_eq_one h d path hb hat hzt y hy x hx
      (by rw [heinv]; exact (centralizer _).inv_mem hbA.2)
    have hb1 : b=1 := by rw [heinv] at hone; exact inv_eq_one.mp hone
    exact hbB (hb1 ▸ one_mem B)
  let := finite_Z d.radical z
  let : Finite B := Finite.of_injective
    (inclusion (show B ≤ Z d.radical z from inf_le_left.trans (U_le_Z z))) (inclusion_injective _)
  have hcard := source_four_large_attachment_card_eq h d g hb hsat path hat hzt c c' hcritical
  exact hne (Subgroup.eq_of_le_of_card_ge hAB hcard.ge)


/-- MS93 (3.7)(4): the two complete fixed attachments agree for every
critical pair at saturated distance two, at the original field degree. -/
theorem source_four_fixed_attachments
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) :
    U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
  by_cases hc : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)
  · exact source_four_large_fixed_attachments h d g hb hsat path hat hzt c c' hc
  · exact source_four_of_field_critical h d g hb hsat path hat hzt c c'
      (replacement_critical_indices_eq_field_of_small h d path (by omega) (lt_of_not_ge hc)).1

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
