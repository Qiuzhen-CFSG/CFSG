module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourMarkedComparison
public import Theory.Representation.SymplecticFourOrthogonalCover.RootOverlap
public import Theory.GroupTheory.FixedSupplementCentralizer
public import Theory.GroupTheory.NormalizedSupConsequences
/-!
# The nonescaping section centralizer and its commutator values

Continue MS93 (3.7)(4), printed p.875, after the full-cover comparison has
excluded an escaping opposite centralizer. For the same marked hyperplane
X, put P = C_T(X), H = [Z,P], B = C_T(X/H), and Y = Z′ ∩ B.
The full plane cover identifies the image of P with the long root of order q.
Since Z′ ∩ P = Z′ ∩ Q, the subgroup indices give T = P Z′,
B = P Y and both [Z′:Y] = [Y:Y ∩ Q] = q. Hence the previously selected
complement A = [X,B] is exactly [X,Y]. Its order q, disjointness from the
entire attachment, and H = A A_Z are retained.

Choose y in Y outside Q. The displacement of X by y is nontrivial, and
its index over the covering kernel is a power of q, because X is the full
preimage of a field-linear hyperplane. Disjointness from the attachment
therefore forces this displacement to fill A. As y is an involution and
X is abelian, its displacement consists of individual commutator values.
Thus every element of A is [y,x] for this same y and some x in X.
The literal Chapter11 application retains the original quotient and action.

The remaining comparison across all hyperplanes, source (5)/(6), and the
field-degree and block conclusions are still required for final assembly.
Private cover transports reuse SourceFourComplement and
SourceFourEscapeComparison; no covering kernel is discarded.
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
private theorem standard_hyperplane_root_image
    (_hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y P _B : Subgroup G) (hPY : P ≤ Y)
    (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hY : ((commutator (Sp F)).subtype.comp β).range=planeRadicalAmbient)
    (hpoint : P=Y ⊓ centralizer (j.range ⊓ centralizer (P : Set G) : Set G))
    (hfix : ∀ w : W, j (Multiplicative.ofAdd w) ∈ centralizer (P : Set G) ↔
      (p w) (.inr 0)=0)
    : (β.comp (inclusion hPY)).range.map (commutator (Sp F)).subtype =
      RootSubgroup.group 0 := by
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
  exact hroot

private theorem marked_hyperplane_root_card
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
    : Nat.card ((((commutator (Sp F)).subtype.comp β₀).comp (inclusion hP)).range) =
      Nat.card F := by
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
  have hr := standard_hyperplane_root_image hlarge p hp j hj Y P B hP β hact hβ
    (by rwa [hjr]) hfix'
  have he : ((commutator (Sp F)).subtype.comp β).comp (inclusion hP) =
      (MulAut.conj k).toMonoidHom.comp
        (((commutator (Sp F)).subtype.comp β₀).comp (inclusion hP)) := by ext; rfl
  have hh : Nat.card ((((commutator (Sp F)).subtype.comp β).comp (inclusion hP)).range) = Nat.card F := by
    change Nat.card (((commutator (Sp F)).subtype.comp (β.comp (inclusion hP))).range)=_
    rw [MonoidHom.range_comp, hr, RootSubgroup.card]
  rw [he,MonoidHom.range_comp,card_map_of_injective (MulAut.conj k).injective] at hh
  exact hh

private theorem embedded_subspace_movement_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : Function.Surjective p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (U Y X : Subgroup G) (hjr : j.range=U) (hYU : Y ≤ normalizer (U : Set G))
    (hXU : X ≤ U) (V : Submodule F (Vector F)) (β : Y →* L (K := F))
    (hact : ∀ y : Y, ∀ w : W, j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hX : ∀ w : W, j (Multiplicative.ofAdd w) ∈ X ↔ p w ∈ V) :
    ∃ r : ℕ, (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j).relIndex ⁅Y,X⁆ =
      Nat.card F^r := by
  let K := p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j
  let α := (commutator (Sp F)).subtype.comp β
  let D : Submodule F (Vector F) := ⨆ y : Y, V.map (symplecticNatural 2 (α y)-LinearMap.id)
  let B := D.toAddSubgroup.toSubgroup
  obtain ⟨π,hπ⟩ := exists_embedded_projection U j hj hjr p.toLinearMap
  have hk : π.ker.map U.subtype=K := by
    apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      obtain ⟨w,hw⟩ := (hjr.symm ▸ u.property : u.val ∈ j.range)
      have he : u=⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
      refine ⟨w,?_,hw⟩
      have hh : π u=1 := hu
      rw [he] at hh
      exact congrArg Multiplicative.toAdd ((hπ w.toAdd).symm.trans hh)
    · rintro x ⟨w,hw,rfl⟩
      refine ⟨⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩,?_,rfl⟩
      change π ⟨j w,_⟩=1
      exact (hπ w.toAdd).trans (congrArg Multiplicative.ofAdd hw)
  have hMU : ⁅Y,X⁆ ≤ U := (commutator_mono le_rfl hXU).trans
    (le_normalizer_iff_commutator_le_right.mp hYU)
  let P := (B.comap π).map U.subtype
  have hMP : ⁅Y,X⁆ ≤ P := by
    apply commutator_le.mpr
    intro y hy x hx
    obtain ⟨w,rfl⟩ := (hjr.symm ▸ hXU hx : x ∈ j.range)
    let v := σ (β ⟨y,hy⟩) w.toAdd-w.toAdd
    refine ⟨⟨j (Multiplicative.ofAdd v),by rw [←hjr]; exact ⟨_,rfl⟩⟩,?_,?_⟩
    · change (π ⟨j (Multiplicative.ofAdd v),_⟩).toAdd ∈ D
      rw [hπ]
      change p v ∈ D
      dsimp only [v]
      rw [map_sub,p.isIntertwining]
      exact (le_iSup (fun y : Y => V.map (symplecticNatural 2 (α y)-LinearMap.id)) ⟨y,hy⟩)
        ⟨p w.toAdd,(hX w.toAdd).mp hx,rfl⟩
    · change j (Multiplicative.ofAdd (σ (β ⟨y,hy⟩) w.toAdd-w.toAdd))=⁅y,j w⁆
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
  have hlift (v : Vector F) (hv : v ∈ D) :
      ∃ w : W, p w=v ∧ j (Multiplicative.ofAdd w) ∈ ⁅Y,X⁆ := by
    refine Submodule.iSup_induction _
      (motive := fun v => ∃ w : W, p w=v ∧ j (Multiplicative.ofAdd w) ∈ ⁅Y,X⁆) hv ?_ ?_ ?_
    · intro y v hv
      obtain ⟨v,hv,rfl⟩ := hv
      obtain ⟨w,rfl⟩ := hp v
      refine ⟨σ (β y) w-w,?_,?_⟩
      · rw [map_sub,p.isIntertwining]
        rfl
      · rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
        exact commutator_mem_commutator y.property ((hX w).mpr hv)
    · exact ⟨0,map_zero _,by simp⟩
    · rintro u v ⟨w,hw,hm⟩ ⟨w',hw',hm'⟩
      refine ⟨w+w',by rw [map_add,hw,hw'],?_⟩
      simpa only [ofAdd_add,map_mul] using (⁅Y,X⁆).mul_mem hm hm'
  have him : (⁅Y,X⁆.subgroupOf U).map π=B := by
    apply le_antisymm
    · rintro v ⟨u,hu,rfl⟩
      obtain ⟨w,hw,he⟩ := hMP hu
      have he' : w=u := Subtype.ext he
      exact he' ▸ hw
    · intro v hv
      obtain ⟨w,hw,hm⟩ := hlift v.toAdd hv
      refine ⟨⟨j (Multiplicative.ofAdd w),by rw [←hjr]; exact ⟨_,rfl⟩⟩,hm,?_⟩
      exact (hπ w).trans (congrArg Multiplicative.ofAdd hw)
  have hi : K.relIndex ⁅Y,X⁆=Nat.card B := by
    rw [←him,←relIndex_ker]
    have he := relIndex_subgroupOf (H := K) hMU
    rw [←hk,subgroupOf_map_subtype_eq] at he
    rw [hk] at he
    exact he.symm
  refine ⟨Module.finrank F D,hi.trans ?_⟩
  let e : B ≃ D :=
    { toFun := fun x => ⟨x.val.toAdd,x.property⟩
      invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := F)]

end Model

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open DistanceTwoRecognition ChapterB.QuasisimpleSource
private theorem plane_cover_fixed_movement_index
    {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) J W} {C₀ : Subgroup J}
    {T : Subgroup M} {s : MovedSection ρ C₀} {n : ℕ} {z t : Vertex T}
    [FiniteDimensional (ZMod 2) s.space.toSubmodule]
    (cv : RadicalPlaneCover T s n z t)
    (Y P : Subgroup (FreeAmalgam T)) (hY : Y ≤ Q T t) (hP : P ≤ Q T t) :
    ∃ r : ℕ, (U T z ⊓ centralizer (Ltilde T z : Set (FreeAmalgam T))).relIndex
      ⁅Y,U T z ⊓ centralizer (P : Set (FreeAmalgam T))⁆ = (2^n)^r := by
  let p := MovedSection.coverProjection s cv.equiv
  let σ := MovedSection.coverAction s cv.equiv
  let β := cv.actor.comp (inclusion hY)
  let γ := cv.actor.comp (inclusion hP)
  let α := (commutator (Sp cv.field.Carrier)).subtype.comp γ
  have hγact (a : P) (w : s.space.toSubmodule) :
      cv.embedding (Multiplicative.ofAdd (σ (γ a) w))=
        a.val*cv.embedding (Multiplicative.ofAdd w)*a.val⁻¹ := cv.actor_conjugation (inclusion hP a) w
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding=
      U T z ⊓ centralizer (Ltilde T z : Set (FreeAmalgam T)) := by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro v ⟨hv,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hv
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  have hf (w : s.space.toSubmodule) :
      cv.embedding (Multiplicative.ofAdd w) ∈ U T z ⊓ centralizer (P : Set (FreeAmalgam T)) ↔
        p w ∈ TwoLocalCover.fixedSpace α.range := by
    constructor
    · intro hw a ha
      obtain ⟨a,rfl⟩ := ha
      have he : σ (γ a) w=w := by
        apply Multiplicative.ofAdd.injective
        apply cv.injective
        rw [hγact,hw.2 a.val a.property,mul_inv_cancel_right]
      exact (LinearMap.congr_fun (p.isIntertwining' (γ a)) w).symm.trans (congrArg p he)
    · intro hw
      refine ⟨cv.range_eq ▸ ⟨_,rfl⟩,fun a ha => ?_⟩
      have he := cover_fixed_of_projection_fixed p cv.cover (γ ⟨a,ha⟩) w
        (hw (α ⟨a,ha⟩) ⟨_,rfl⟩)
      have he' := congrArg (fun v => cv.embedding (Multiplicative.ofAdd v)) he
      change cv.embedding (Multiplicative.ofAdd (σ (γ ⟨a,ha⟩) w))=_ at he'
      rw [hγact,mul_inv_eq_iff_eq_mul] at he'
      exact he'
  obtain ⟨r,hr⟩ := embedded_subspace_movement_index p cv.cover.1 cv.embedding cv.injective
    (U T z) Y (U T z ⊓ centralizer (P : Set (FreeAmalgam T))) cv.range_eq
    ((hY.trans cv.edge_le).trans (U_normalized z)) inf_le_left
    (TwoLocalCover.fixedSpace α.range) β (fun y w => cv.actor_conjugation (inclusion hY y) w) hf
  rw [hk,cv.field.card_eq,cv.degree] at hr
  exact ⟨r,hr⟩

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem marked_fixer_card
    {z t : Vertex d.radical} (P B : Subgroup (FreeAmalgam d.radical))
    (hm : HasMarkedHyperplane h d z t P B) :
    (Q d.radical z).relIndex P=2^n ∧
      (Q d.radical z).relIndex (Q d.radical t)=(2^n)^3 := by
  obtain ⟨cv,k,hk,hP,_,hp,hfix,_⟩ := hm
  have hc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  have hlarge : 2 < Nat.card cv.field.Carrier := by
    rw [hc]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  have hh := marked_hyperplane_root_card hlarge
    (MovedSection.coverProjection (replacementMovedSection h d) cv.equiv) cv.cover
    cv.embedding cv.injective (Q d.radical t) cv.actor cv.actor_conjugation k hk P B hP
    (by simpa only [cv.range_eq] using hp) hfix
  rw [←index_ker,←MonoidHom.comap_ker,cv.actor_kernel,comap_inclusion_subgroupOf,hc] at hh
  exact ⟨hh,cv.radical_index⟩

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem nonescaping_section_factors
    {G : Type*} [Group G] (T Q V P B X : Subgroup G) [Finite T]
    (q : ℕ) (hq : 0<q)
    (_hQT : Q ≤ T) (hVT : V ≤ T) (hQP : Q ≤ P) (hPB : P ≤ B) (hBT : B ≤ T)
    (hPX : P ≤ centralizer (X : Set G)) (hTX : T ≤ normalizer (X : Set G))
    (hTP : T ≤ normalizer (P : Set G)) (hVP : V ⊓ P=V ⊓ Q)
    (hQi : Q.relIndex T=q^3) (hPi : Q.relIndex P=q)
    (hVi : Q.relIndex V=q^2) (hBi : B.relIndex T=q) :
    let Y := V ⊓ B
    Y.relIndex V=q ∧ Q.relIndex Y=q ∧
      T=P ⊔ V ∧ B=P ⊔ Y ∧ ⁅X,B⁆=⁅X,Y⁆ := by
  let Y := V ⊓ B
  have hPT : P ≤ T := hPB.trans hBT
  have hYP : P.relIndex V=q^2 := by rw [←inf_relIndex_left,hVP,inf_relIndex_left,hVi]
  have hPTi : P.relIndex T=q^2 := by
    have hh := relIndex_mul_relIndex Q P T hQP hPT
    rw [hPi,hQi] at hh
    nlinarith only [hh,hq]
  have hPV : P.relIndex (P ⊔ V)=P.relIndex V := by
    let J := P ⊔ V
    let : (P.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
      ((sup_le hPT hVT).trans hTP)
    have hh := relIndex_sup_left (V.subgroupOf J) (P.subgroupOf J)
    rw [←subgroupOf_sup (show P ≤ J from le_sup_left) (show V ≤ J from le_sup_right),
      relIndex_subgroupOf (show J ≤ J from le_rfl),relIndex_subgroupOf (show V ≤ J from le_sup_right)] at hh
    exact hh
  have hjoin : T=P ⊔ V := by
    have hh := relIndex_mul_relIndex P (P ⊔ V) T le_sup_left (sup_le hPT hVT)
    rw [hPV,hYP,hPTi] at hh
    have he : (P ⊔ V).relIndex T=1 := by nlinarith only [hh,hq]
    exact le_antisymm (relIndex_eq_one.mp he) (sup_le hPT hVT)
  have hBjoin : B=P ⊔ Y := by
    apply le_antisymm ?_ (sup_le hPB inf_le_right)
    intro b hb
    have hbT := hBT hb
    rw [hjoin,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ (hVT.trans hTP)] at hbT
    obtain ⟨p,hp,v,hv,he⟩ := hbT
    have hvB : v ∈ B := by
      have hh := B.mul_mem (B.inv_mem (hPB hp)) hb
      rwa [←he,inv_mul_cancel_left] at hh
    rw [←he]
    exact (P ⊔ Y).mul_mem (mem_sup_left hp) (mem_sup_right ⟨hv,hvB⟩)
  have hPBi : P.relIndex B=q := by
    have hh := relIndex_mul_relIndex P B T hPB hBT
    rw [hBi,hPTi] at hh
    nlinarith only [hh,hq]
  have hPY : P.relIndex Y=q := by
    let J := P ⊔ Y
    let : (P.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
      ((sup_le hPT (inf_le_left.trans hVT)).trans hTP)
    have hh := relIndex_sup_left (Y.subgroupOf J) (P.subgroupOf J)
    rw [←subgroupOf_sup (show P ≤ J from le_sup_left) (show Y ≤ J from le_sup_right),
      relIndex_subgroupOf (show J ≤ J from le_rfl),relIndex_subgroupOf (show Y ≤ J from le_sup_right)] at hh
    change P.relIndex (P ⊔ Y)=P.relIndex Y at hh
    rw [←hBjoin,hPBi] at hh
    exact hh.symm
  have hYmeet : Y ⊓ P=Y ⊓ Q := by
    apply le_antisymm
    · rintro x ⟨hx,hp⟩
      exact ⟨hx,(hVP.le ⟨hx.1,hp⟩).2⟩
    · exact inf_le_inf_left _ hQP
  have hQY : Q.relIndex Y=q := by rw [←inf_relIndex_left,←hYmeet,inf_relIndex_left,hPY]
  have hCY : V ⊓ Q ≤ Y := le_inf inf_le_left (inf_le_right.trans (hQP.trans hPB))
  have hi : Y.relIndex V=q := by
    have hh := relIndex_mul_relIndex (V ⊓ Q) Y V hCY inf_le_left
    have hm : Y ⊓ (V ⊓ Q)=Y ⊓ Q := by
      rw [←inf_assoc,inf_eq_left.mpr (show Y ≤ V from inf_le_left)]
    have hmidx : (V ⊓ Q).relIndex Y=Q.relIndex Y := by
      rw [←inf_relIndex_left Y (V ⊓ Q),hm,inf_relIndex_left]
    have hh' : q*Y.relIndex V=q^2 := by
      simpa only [hmidx,hQY,inf_relIndex_left V Q,hVi] using hh
    nlinarith only [hh',hq]
  refine ⟨hi,hQY,hjoin,hBjoin,?_⟩
  apply le_antisymm ?_ (commutator_mono le_rfl inf_le_right)
  apply commutator_le_moving_of_inner_mod_centralizer X Y B
    ((inf_le_left.trans hVT).trans hTX)
  rw [hBjoin,sup_comm P Y]
  exact sup_le_sup_left hPX Y

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem involution_row_values
    {G : Type*} [Group G] (X : Subgroup G) [IsMulCommutative X]
    (y : G) (hy : y ∈ normalizer (X : Set G)) (ho : orderOf y=2)
    (v : G) (hv : v ∈ ⁅X,zpowers y⁆) : ∃ x ∈ X, ⁅x,y⁆=v := by
  let f : X →* G :=
    { toFun x := ⁅x.val,y⁆
      map_one' := by simp
      map_mul' x z := by
        have hm : ⁅z.val,y⁆ ∈ X := by
          have hn : zpowers y ≤ normalizer (X : Set G) := zpowers_le.mpr hy
          exact (le_normalizer_iff_commutator_le_left.mp hn)
            (commutator_mem_commutator z.property (mem_zpowers y))
        have hc := X.le_centralizer x.property _ hm
        change ⁅x.val*z.val,y⁆=_
        rw [commutatorElement_mul_left_eq_conj_mul,←hc,mul_inv_cancel_right]
        exact (X.le_centralizer hm _ (by
          have hn : zpowers y ≤ normalizer (X : Set G) := zpowers_le.mpr hy
          exact (le_normalizer_iff_commutator_le_left.mp hn)
            (commutator_mem_commutator x.property (mem_zpowers y)))).symm }
  have hm : ⁅X,zpowers y⁆ ≤ f.range := by
    apply commutator_le.mpr
    intro x hx b hb
    have hb' : b=1 ∨ b=y := by
      classical
      have hyfin : IsOfFinOrder y := orderOf_pos_iff.mp (by omega)
      rw [hyfin.mem_zpowers_iff_mem_range_orderOf,ho] at hb
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
      have hi2 : i<2 := Finset.mem_range.mp hi
      interval_cases i <;> simp
    rcases hb' with rfl | rfl
    · simp only [commutatorElement_one_right,one_mem]
    · exact ⟨⟨x,hx⟩,rfl⟩
  obtain ⟨x,hx⟩ := hm hv
  exact ⟨x.val,x.property,hx⟩

private theorem full_hyperplane_movement_index
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {z t : Vertex d.radical} (hz : color d.radical z=false)
    (hzt : Adjacent d.radical z t)
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (P Y : Subgroup (FreeAmalgam d.radical)) (hP : P ≤ Q d.radical t) (hY : Y ≤ Q d.radical t) :
    ∃ r : ℕ, (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))).relIndex
      ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Y⁆=(2^n)^r := by
  let C := Z d.radical t
  let X₀ := U d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (hz.trans he.symm)
  have hCT : C ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [show C=omegaCenter (Q d.radical t) by simp [C,Z,ht,edgeOmega]]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hCZ : C ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical hz hzt
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z hz
  have hCU : C ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCX : C ≤ normalizer (X₀ : Set (FreeAmalgam d.radical)) :=
    (hCZ.trans ((Z d.radical z).le_centralizer.trans (centralizer_le
      (inf_le_left.trans (U_le_Z z))))).trans (Subgroup.centralizer_le_normalizer _)
  have hX : Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))=X₀ ⊔ C := by
    rw [Z_eq_moving_sup_edge_of_distance_two h d g hb hz hzt,
      sup_comm (U d.radical z),inf_centralizer_sup_of_centralizing C (U d.radical z) P
        hCU (hCT.trans (centralizer_le hP)),sup_comm]
  have he : ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Y⁆=⁅Y,X₀⁆ := by
    rw [commutator_comm,hX]
    apply le_antisymm ?_ (commutator_mono le_rfl le_sup_left)
    apply commutator_le.mpr
    intro y hy x hx
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCX] at hx
    obtain ⟨u,hu,c,hc,rfl⟩ := hx
    have hyc : Commute y c := hCT hc y (hY hy)
    rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hyc]
    simpa only [mul_one,mul_inv_cancel_right] using commutator_mem_commutator hy hu
  obtain ⟨r,hr⟩ := plane_cover_fixed_movement_index cv Y P hY hP
  rw [he]
  exact ⟨r,hr⟩

private theorem nonescaping_complement_values
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {a z t : Vertex d.radical} (ha : color d.radical a=false) (hz : color d.radical z=false)
    (hzt : Adjacent d.radical z t)
    (P B : Subgroup (FreeAmalgam d.radical))
    (hm : HasMarkedHyperplane h d z t P B)
    (_hVT : Z d.radical a ≤ Q d.radical t) (hBT : B ≤ Q d.radical t)
    (hTX : Q d.radical t ≤ normalizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hpoint : P=Q d.radical t ⊓ centralizer
      (Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hVP : Z d.radical a ⊓ P=Z d.radical a ⊓ Q d.radical z)
    (hYq : (Q d.radical z).relIndex (Z d.radical a ⊓ B)=2^n)
    (hdis : Disjoint ⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a ⊓ B⁆
      (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))))
    (hcard : Nat.card (⁅Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical)),Z d.radical a ⊓ B⁆ :
      Subgroup (FreeAmalgam d.radical))=2^n) :
    let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
    let Y := Z d.radical a ⊓ B
    ∃ y ∈ Y, y ∉ Q d.radical z ∧ ∀ v ∈ ⁅X,Y⁆, ∃ x ∈ X, ⁅y,x⁆=v := by
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let Y := Z d.radical a ⊓ B
  let A := ⁅X,Y⁆
  let A₀ := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  have hq : 1<2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  have hnot : ¬ Y ≤ Q d.radical z := by
    intro he
    have hi := relIndex_eq_one.mpr he
    rw [hYq] at hi
    omega
  obtain ⟨y,hy,hyQ⟩ := SetLike.not_le_iff_exists.mp hnot
  have hyP : y ∉ P := fun hp => hyQ ((hVP.le ⟨hy.1,hp⟩).2)
  have hyT : y ∈ Q d.radical t := hBT hy.2
  have hyC : y ∉ centralizer (X : Set (FreeAmalgam d.radical)) := by
    intro hc
    exact hyP (hpoint.ge ⟨hyT,hc⟩)
  let D := ⁅X,zpowers y⁆
  have hDA : D ≤ A := commutator_mono le_rfl (zpowers_le.mpr hy)
  have hne : D ≠ ⊥ := by
    intro he
    have hc := commutator_eq_bot_iff_le_centralizer.mp he
    exact hyC (le_centralizer_iff.mp hc (mem_zpowers y))
  obtain ⟨cv,k,hk,hP,_⟩ := hm
  obtain ⟨r,hr⟩ := full_hyperplane_movement_index h d g hb hz hzt cv P (zpowers y) hP
    (zpowers_le.mpr hyT)
  have hdisD : Disjoint D A₀ := hdis.mono_left hDA
  have hDr : Nat.card D=(2^n)^r := by
    rw [←inf_relIndex_left,inf_comm D A₀,disjoint_iff.mp hdisD.symm,relIndex_bot_left] at hr
    exact hr
  let := finite_Z d.radical z
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z hz
  let : IsMulCommutative X := ⟨⟨fun x y => Subtype.ext
    ((Z d.radical z).le_centralizer y.property.1 x.val x.property.1)⟩⟩
  have hAX : A ≤ X := le_normalizer_iff_commutator_le_left.mp
    ((inf_le_right.trans hBT).trans hTX)
  let : Finite A := Finite.of_injective (inclusion (hAX.trans inf_le_left)) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDA) (inclusion_injective _)
  have hrpos : 1 ≤ r := by
    by_contra hn
    have hr0 : r=0 := by omega
    exact hne (Subgroup.card_eq_one.mp (by simpa [hr0] using hDr))
  have hlow : 2^n ≤ Nat.card D := by
    rw [hDr]
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < 2^n) hrpos
  have heq : D=A := Subgroup.eq_of_le_of_card_ge hDA (by rw [hcard]; exact hlow)
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a ha
  have ho : orderOf y=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian y hy.1) (fun he => hyQ (he ▸ one_mem _))
  refine ⟨y,hy,hyQ,fun v hv => ?_⟩
  obtain ⟨x,hx,he⟩ := involution_row_values X y (hTX hyT) ho v⁻¹ (D.inv_mem (heq.ge hv))
  refine ⟨x,hx,?_⟩
  rw [←commutatorElement_inv,he,inv_inv]

/-- The nonescaping section centralizer from source (4), with its literal
membership condition, both field indices and the complete complement.
Every complement element is an individual commutator of the original
Z-layers, with one fixed nontrivial actor in the section centralizer. -/
theorem source_four_large_unequal_nonescaping_section
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
      let Y := Z d.radical a ⊓ B
      HasMarkedHyperplane h d z t P B ∧ P ≤ Q d.radical t ∧ B ≤ Q d.radical t ∧
      X.relIndex (Z d.radical z)=2^n ∧
      (∀ y : FreeAmalgam d.radical, y ∈ Y ↔ y ∈ Z d.radical a ∧ ∀ x ∈ X, ⁅y,x⁆ ∈ H₀) ∧
      Y.relIndex (Z d.radical a)=2^n ∧ (Q d.radical z).relIndex Y=2^n ∧
      Q d.radical t=P ⊔ Z d.radical a ∧ B=P ⊔ Y ∧
      ⁅X,B⁆=⁅X,Y⁆ ∧ Disjoint ⁅X,Y⁆ A₀ ∧
      Nat.card (⁅X,Y⁆ : Subgroup (FreeAmalgam d.radical))=2^n ∧
      H₀=⁅X,Y⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z d.radical a,Z d.radical z⁆ ∧
      ∃ y ∈ Y, y ∉ Q d.radical z ∧ ∀ v ∈ ⁅X,Y⁆, ∃ x ∈ X, ⁅y,x⁆=v := by
  obtain ⟨P,B,hm,hQP,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi,hno⟩ :=
    source_four_large_unequal_nonescaping_hyperplane h d g hb hsat path hat hzt c c' hcritical hne
  let X := Z d.radical z ⊓ centralizer (P : Set (FreeAmalgam d.radical))
  let Y := Z d.radical a ⊓ B
  have haT : Z d.radical a ≤ Q d.radical t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      ((omegaCenter_le _).trans c.core_le_edge)
  have hPX : P ≤ centralizer (X : Set (FreeAmalgam d.radical)) := hpoint.le.trans inf_le_right
  have hTX : Q d.radical t ≤ normalizer (X : Set (FreeAmalgam d.radical)) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    have hfull := source_four_large_full_movement h d g hb hsat path hat hzt c c' hcritical
    exact (commutator_mono le_rfl (show X ≤ Z d.radical z from inf_le_left)).trans
      (hfull.le.trans hRX)
  have hTP : Q d.radical t ≤ normalizer (P : Set (FreeAmalgam d.radical)) := by
    rw [hpoint]
    exact (le_inf (Q d.radical t).le_normalizer
      (hTX.trans (normalizer_le_normalizer_centralizer X))).trans inf_normalizer_le_normalizer_inf
  have hPB : P ≤ B := by
    intro p hp
    apply (hmem p).mpr
    refine ⟨hP hp,fun x hx => ?_⟩
    rw [commutatorElement_eq_one_iff_commute.mpr (hPX hp x hx).symm]
    exact one_mem _
  have hVP : Z d.radical a ⊓ P=Z d.radical a ⊓ Q d.radical z := by
    apply le_antisymm ?_ (inf_le_inf_left _ hQP)
    rintro x ⟨hx,hp⟩
    exact ⟨hx,hno ⟨hx,hPX hp⟩⟩
  obtain ⟨hPi,hQi⟩ := marked_fixer_card h d P B hm
  have hVi := (source_four_large_midpoint_kernels h d g hb hsat path hat hzt c c' hcritical).2.2.1
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion c'.edge_le) (inclusion_injective _)
  obtain ⟨hYi,hYq,hTjoin,hBjoin,hmove⟩ := nonescaping_section_factors
    (Q d.radical t) (Q d.radical z) (Z d.radical a) P B X (2^n) (by positivity)
    c'.core_le_edge haT hQP hPB hB hPX hTX hTP hVP hQi hPi hVi hBi
  refine ⟨P,B,hm,hP,hB,hi,?_,hYi,hYq,hTjoin,hBjoin,hmove,?_,?_,?_,hR,?_⟩
  · intro y
    constructor
    · rintro ⟨hy,hbY⟩
      exact ⟨hy,((hmem y).mp hbY).2⟩
    · rintro ⟨hy,hyX⟩
      exact ⟨hy,(hmem y).mpr ⟨haT hy,hyX⟩⟩
  · exact hmove ▸ hdis
  · exact hmove ▸ hcard
  · exact hmove ▸ hjoin
  · exact nonescaping_complement_values h d g hb path.start_color path.end_color hzt
      P B hm haT hB hTX hpoint hVP hYq (hmove ▸ hdis) (hmove ▸ hcard)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
