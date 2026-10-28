module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefActors.Coordinates
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.MarkedResiduals
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Compatible marked factors on the two original chief modules

The common quotient kernel and paired base align the two natural chief
coordinate systems. A base-preserving automorphism permutes the two S₃
factors: an involution centralizing a nontrivial cubic element of SL₂(2)
is trivial, so the image of either factor is supported in one coordinate.
Only calculations in SL₂(2) and on the sixteen natural vectors are finite.

Each original marked plane is its factor's action commutator. The literal
Sylow subgroup supplies an element whose quotient image is an involution
interchanging the planes on both chief factors. The embedded residuals of
the marked factors are interchanged by the same conjugation, and either
one normally generates O²(H). The final consumer retains the original
chief intervals, actor maps, Sylow subgroup and ambient residual embedding.

This supplies the simultaneous-marking and residual-generation clauses of
Notation 15.2.9 and the proof of 15.2.11. It does not yet place every
original Delta member in one marked factor or identify its quotient image
as order two. Those offender and X-generation steps remain with
qt-e-152-offender-plane. The preceding uniqueness and wreath hypotheses
come from qt-e-152-small-parabolic; qt-e-152-plane-geometry retains their
final discharge.

Source: Aschbacher--Smith, Notation 15.2.9 and Lemma 15.2.11,
printed pp.1110--1111; refs/quasithin.pdf.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

private theorem sl2_words : ∀ a : SL2,
    a=1 ∨ a=transvection false ∨ a=transvection true ∨
    a=transvection false*transvection true ∨ a=transvection true*transvection false ∨
    a=transvection false*transvection true*transvection false := by
  decide +kernel

private theorem cubic_centralizer : ∀ a b : SL2,
    a^2=1 → b^3=1 → b≠1 → a*b=b*a → a=1 := by
  decide +kernel

private def cubic : SL2 := transvection false * transvection true

private theorem cubic_order : cubic^3=1 ∧ cubic≠1 := by decide +kernel

private theorem coordinate_commute (i : C2) (a b : SL2) :
    coordinate i a * coordinate (flip*i) b = coordinate (flip*i) b * coordinate i a := by
  ext j
  · by_cases hj : j=i
    · subst j
      simp [coordinate,Ne.symm (opposite_ne i)]
    · simp [coordinate,hj]
  · simp [coordinate]

private theorem left_pow (g : Actor) (hg : g.right=1) (n : ℕ) (j : C2) :
    (g^n).left j = (g.left j)^n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ,RegularWreathProduct.mul_left]
    have hr : (g^n).right=1 := by
      change RegularWreathProduct.rightHom (g^n)=1
      rw [map_pow]
      change g.right^n=1
      rw [hg,one_pow]
    simp only [hr,inv_one,one_mul,Pi.mul_apply,hn,pow_succ]

private theorem factor_card (i : C2) : Nat.card (factor i)=6 := by
  rw [Nat.card_congr (factorEquiv i).toEquiv,Nat.card_eq_fintype_card]
  decide +kernel

/-- A base-preserving automorphism permutes the two literal factors. -/
theorem factor_map_of_base (e : Actor ≃* Actor)
    (he : base.map e.toMonoidHom = base) (i : C2) :
    ∃ j : C2, (factor i).map e.toMonoidHom = factor j := by
  have hb (a : Actor) (ha : a.right=1) : (e a).right=1 := by
    have hh := mem_map_of_mem e.toMonoidHom (show a∈base from ha)
    rw [he] at hh
    exact hh
  let z := e (coordinate (flip*i) cubic)
  have hz : z^3=1 := by
    dsimp [z]
    rw [←map_pow,←map_pow,cubic_order.1,map_one,map_one]
  have hzn : z≠1 := by
    intro hh
    have hh' := e.injective (hh.trans e.map_one.symm)
    exact cubic_order.2 ((coordinate_injective (flip*i)) (hh'.trans (map_one _).symm))
  have hzb : z.right=1 := hb _ rfl
  obtain ⟨j,hj⟩ : ∃ j, z.left j≠1 := by
    by_contra hn
    push Not at hn
    exact hzn (RegularWreathProduct.ext (funext hn) hzb)
  have hgen (b : Bool) : e (coordinate i (transvection b)) ∈ factor (flip*j) := by
    let x := e (coordinate i (transvection b))
    have hxb : x.right=1 := hb _ rfl
    have hx : x^2=1 := by
      dsimp [x]
      rw [←map_pow,←map_pow,(transvection_involution b).1,map_one,map_one]
    have hcomm : x*z=z*x := by
      exact (map_mul e _ _).symm.trans ((congrArg e (coordinate_commute i _ _)).trans (map_mul e _ _))
    have hjx : x.left j=1 := cubic_centralizer _ _
      ((left_pow x hxb 2 j).symm.trans (congrArg (fun a : Actor => a.left j) hx))
      ((left_pow z hzb 3 j).symm.trans (congrArg (fun a : Actor => a.left j) hz)) hj
      (by simpa [hxb,hzb] using congrArg (fun a : Actor => a.left j) hcomm)
    apply (mem_factor _ _).mpr
    refine ⟨hxb,?_⟩
    intro k hk
    have hkj : k=j := by
      rcases index_cases k with rfl | rfl <;> rcases index_cases j with rfl | rfl <;>
        simp_all [flip]
    exact hkj ▸ hjx
  have hle : (factor i).map e.toMonoidHom ≤ factor (flip*j) := by
    rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    rcases sl2_words a with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [map_one]; exact one_mem _
    · exact hgen false
    · exact hgen true
    · simp only [map_mul]; exact mul_mem (hgen false) (hgen true)
    · simp only [map_mul]; exact mul_mem (hgen true) (hgen false)
    · simp only [map_mul]; exact mul_mem (mul_mem (hgen false) (hgen true)) (hgen false)
  refine ⟨flip*j,eq_of_le_of_card_ge hle ?_⟩
  rw [card_map_of_injective e.injective,factor_card,factor_card]

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

private theorem factor_ne_opposite (i : C2) : factor i ≠ factor (flip*i) := by
  intro h
  have hm : coordinate i (transvection false) ∈ factor (flip*i) := h ▸ ⟨_,rfl⟩
  have hh := ((mem_factor _ _).mp hm).2 i (Ne.symm (opposite_ne i))
  exact (transvection_involution false).2 (by simpa [coordinate] using hh)

/-- The alignment uses the actual surjections, their common kernel and base. -/
theorem align_factor_preimages {D : Type*} [Group D]
    (f g : D →* Actor) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hk : f.ker=g.ker) (hb : base.comap f=base.comap g) :
    ∃ j : C2, (factor 1).comap f = (factor j).comap g ∧
      (factor flip).comap f = (factor (flip*j)).comap g := by
  let a := QuotientGroup.quotientKerEquivOfSurjective f hf
  let e := a.symm.trans (QuotientGroup.liftEquiv f.ker hg hk)
  have he (x : D) : e (f x)=g x := by
    change QuotientGroup.liftEquiv f.ker hg hk (a.symm (f x)) = _
    rw [show a.symm (f x)=QuotientGroup.mk' f.ker x from
      (MulEquiv.symm_apply_eq a).mpr rfl]
    rfl
  have heb : base.map e.toMonoidHom=base := by
    apply le_antisymm
    · rintro _ ⟨y,hy,rfl⟩
      obtain ⟨x,rfl⟩ := hf y
      change e (f x)∈base
      rw [he]
      exact show x∈base.comap g from hb ▸ (show x∈base.comap f from hy)
    · intro y hy
      obtain ⟨x,rfl⟩ := hg y
      refine ⟨f x,?_,he x⟩
      exact show x∈base.comap f from hb.symm ▸ (show x∈base.comap g from hy)
  have hpre (i j : C2) (hij : (factor i).map e.toMonoidHom=factor j) :
      (factor i).comap f=(factor j).comap g := by
    ext x
    change f x∈factor i ↔ g x∈factor j
    rw [←hij]
    constructor
    · intro hx; exact ⟨f x,hx,he x⟩
    · rintro ⟨y,hy,hyx⟩
      have hh : y=f x := e.injective (hyx.trans (he x).symm)
      exact hh ▸ hy
  obtain ⟨j,hj⟩ := factor_map_of_base e heb 1
  obtain ⟨k,hk'⟩ := factor_map_of_base e heb flip
  have hkj : k≠j := by
    intro hh
    have heq : factor 1=factor flip := (map_injective e.injective) (hj.trans (hh ▸ hk').symm)
    exact factor_ne_opposite 1 (by simpa using heq)
  have hkj' : k=flip*j := by
    rcases index_cases k with rfl | rfl <;> rcases index_cases j with rfl | rfl <;>
      simp_all [flip]
  exact ⟨j,hpre 1 j hj,hkj' ▸ hpre flip k hk'⟩

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates
open Representation
variable {D W W' : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup W'] [Module (ZMod 2) W']
  {ρ : Representation (ZMod 2) D W} {σ : Representation (ZMod 2) D W'}

/-- Natural coordinates with a common kernel and paired base have the same
two marked factors, up to one simultaneous interchange. -/
theorem factors_align (c : ChiefWreathCoordinates ρ) (d : ChiefWreathCoordinates σ)
    (hk : c.actor.ker=d.actor.ker)
    (hb : c.factor 1 ⊔ c.factor ChiefWreath.flip = d.factor 1 ⊔ d.factor ChiefWreath.flip) :
    ∃ j : ChiefWreath.C2, c.factor 1 = d.factor j ∧
      c.factor ChiefWreath.flip = d.factor (ChiefWreath.flip*j) := by
  rw [c.factor_sup_eq_base,d.factor_sup_eq_base] at hb
  exact ChiefWreath.align_factor_preimages c.actor d.actor c.surjective d.surjective hk hb

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

private theorem coordinate_displacement (i : C2) (a : SL2) (v : Space) :
    v⁻¹ * action (coordinate i a) v ∈ plane i := by
  intro j hj
  simp [action,coordinate,hj]

private theorem plane_is_displacement : ∀ (i : C2) (v : Space),
    (∀ j, j≠i → v j=1) →
      ∃ w : Space, w⁻¹ * action (coordinate i cubic) w=v := by
  decide +kernel

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates
open Representation
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W}

/-- Each marked chief plane is the literal action commutator of its factor. -/
theorem factor_support (c : ChiefWreathCoordinates ρ) (i : ChiefWreath.C2) :
    letI := BinaryGroupAction.action ρ
    commutatorAction (c.factor i) (Multiplicative W)=c.plane i := by
  let := BinaryGroupAction.action ρ
  rw [commutatorAction_eq_closure]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g,v,rfl⟩
    change c.vectors (v⁻¹ * (g.val • v))∈ChiefWreath.plane i
    rw [map_mul,map_inv]
    change (c.vectors v)⁻¹ * c.vectors (Multiplicative.ofAdd (ρ g.val v.toAdd))∈_
    rw [c.vectors_action]
    obtain ⟨a,ha⟩ := g.property
    rw [←ha]
    exact ChiefWreath.coordinate_displacement i a (c.vectors v)
  · intro v hv
    obtain ⟨w,hw⟩ := ChiefWreath.plane_is_displacement i (c.vectors v) hv
    obtain ⟨g,hg⟩ := c.surjective (ChiefWreath.coordinate i ChiefWreath.cubic)
    have hgm : g∈c.factor i := by
      change c.actor g∈ChiefWreath.factor i
      rw [hg]
      exact ⟨_,rfl⟩
    apply Subgroup.subset_closure
    refine ⟨⟨g,hgm⟩,c.vectors.symm w,?_⟩
    symm
    apply c.vectors.injective
    change c.vectors ((c.vectors.symm w)⁻¹ *
      Multiplicative.ofAdd (ρ g (c.vectors.symm w).toAdd)) = c.vectors v
    rw [map_mul,map_inv,c.vectors_action,hg,c.vectors.apply_symm_apply]
    exact hw

/-- Conjugation interchanges the actual chief planes according to the same
wreath permutation as the marked factors. -/
theorem plane_conj (c : ChiefWreathCoordinates ρ) (g : D) (i : ChiefWreath.C2) :
    letI := BinaryGroupAction.action ρ
    (c.plane i).map (MulDistribMulAction.toMulAut D (Multiplicative W) g).toMonoidHom =
      c.plane ((c.actor g).right*i) := by
  let := BinaryGroupAction.action ρ
  rw [←c.factor_support i,ActionSupport.commutatorAction_conjBy]
  have hh : (c.factor i).conjBy g=c.factor ((c.actor g).right*i) := c.factor_conj g i
  exact (congrArg (fun A : Subgroup D => commutatorAction A (Multiplicative W)) hh).trans
    (c.factor_support _)

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates


namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

/-- Every actual Sylow subgroup contains an involution interchanging the planes. -/
theorem sylow_interchange (S : Sylow 2 Actor) :
    ∃ t∈(S : Subgroup Actor), t^2=1 ∧ t.right=flip := by
  let b : Actor := RegularWreathProduct.inl flip
  have hb : b^2=1 := by
    change (RegularWreathProduct.inl flip : Actor)^2=1
    rw [←map_pow,show flip^2=1 from by decide,map_one]
  have hp : IsPGroup 2 (zpowers b) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one hb).isPGroup 2 _
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Actor P S
  have hm : (P : Subgroup Actor).map (MulAut.conj g).toMonoidHom = S := by
    change ((g • P : Sylow 2 Actor) : Subgroup Actor)=_
    rw [hg]
  refine ⟨g*b*g⁻¹,?_,?_,?_⟩
  · exact hm ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom (hP (mem_zpowers b))
  · rw [conj_pow,hb]; simp
  · simp [b,mul_comm]

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates
open Representation
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W}

/-- The interchanging involution in the image lifts into the specified Sylow
subgroup, with its literal effects on all marked planes and factors. -/
theorem sylow_interchange (c : ChiefWreathCoordinates ρ) (S : Sylow 2 D) :
    ∃ t∈(S : Subgroup D), (c.actor t)^2=1 ∧ (c.actor t).right=ChiefWreath.flip ∧
      (∀ i, (c.factor i).map (MulAut.conj t).toMonoidHom = c.factor (ChiefWreath.flip*i)) ∧
      (letI := BinaryGroupAction.action ρ
        ∀ i, (c.plane i).map (MulDistribMulAction.toMulAut D (Multiplicative W) t).toMonoidHom =
          c.plane (ChiefWreath.flip*i)) := by
  obtain ⟨y,hy,hy2,hyr⟩ := ChiefWreath.sylow_interchange (S.mapSurjective c.surjective)
  obtain ⟨t,ht,rfl⟩ := hy
  refine ⟨t,ht,hy2,hyr,?_,?_⟩
  · intro i
    rw [c.factor_conj,hyr]
  · let := BinaryGroupAction.action ρ
    intro i
    rw [c.plane_conj,hyr]

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates
open Representation
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W}

omit [Finite D] in
/-- The two-residual lies in the kernel of the factor permutation. -/
theorem residual_le_base (c : ChiefWreathCoordinates ρ) :
    pResidual 2 D ≤ ChiefWreath.base.comap c.actor := by
  exact pResidual_le_ker_of_isPGroup 2 (RegularWreathProduct.rightHom.comp c.actor)
    (IsPGroup.of_card (n:=1) (by simp [Nat.card_eq_fintype_card]))

/-- The marked residuals transform with their actual centralizer factors. -/
theorem residualFactor_conj (c : ChiefWreathCoordinates ρ) (g : D) (i : ChiefWreath.C2) :
    (c.residualFactor i).map (MulAut.conj g).toMonoidHom =
      c.residualFactor ((c.actor g).right*i) := by
  change ((pResidual 2 (c.factor i)).map (c.factor i).subtype).map _ = _
  rw [map_embedded_pResidual]
  exact congrArg (fun A : Subgroup D => (pResidual 2 A).map A.subtype) (c.factor_conj g i)

/-- Either distinguished residual normally generates the full two-residual. -/
theorem residualFactor_span (c : ChiefWreathCoordinates ρ) (i : ChiefWreath.C2) :
    conjugateSpanBy (c.residualFactor i) ⊤ = pResidual 2 D := by
  have hpair : c.residualFactor i ⊔ c.residualFactor (ChiefWreath.flip*i)=pResidual 2 D := by
    rcases ChiefWreath.index_cases i with rfl | rfl
    · simpa using c.residualFactors_span c.residual_le_base
    · simpa [sup_comm,ChiefWreath.flip] using c.residualFactors_span c.residual_le_base
  apply le_antisymm
  · exact conjugateSpanBy_le (c.residualFactor_le i) le_normalizer_of_normal
  · rw [←hpair]
    refine sup_le (le_conjugateSpanBy _ _) ?_
    obtain ⟨t,ht⟩ := c.surjective (RegularWreathProduct.inl ChiefWreath.flip)
    have htr : (c.actor t).right=ChiefWreath.flip := by rw [ht]; rfl
    rw [←htr,←c.residualFactor_conj t i,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup_of_le (⟨t,mem_top t⟩ : (⊤ : Subgroup D)) le_rfl

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates
open Representation
variable {D W W' : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup W'] [Module (ZMod 2) W']
  {ρ : Representation (ZMod 2) D W} {σ : Representation (ZMod 2) D W'}

/-- A common paired base gives the identical factor permutation on both modules. -/
theorem right_eq_of_common_base (c : ChiefWreathCoordinates ρ) (d : ChiefWreathCoordinates σ)
    (hb : c.factor 1 ⊔ c.factor ChiefWreath.flip = d.factor 1 ⊔ d.factor ChiefWreath.flip)
    (g : D) : (c.actor g).right = (d.actor g).right := by
  rw [c.factor_sup_eq_base,d.factor_sup_eq_base] at hb
  have hh : (c.actor g).right=1 ↔ (d.actor g).right=1 :=
    show g∈ChiefWreath.base.comap c.actor ↔ g∈ChiefWreath.base.comap d.actor from
      SetLike.ext_iff.mp hb g
  rcases ChiefWreath.index_cases (c.actor g).right with hc | hc <;>
    rcases ChiefWreath.index_cases (d.actor g).right with hd | hd <;>
    simp_all [ChiefWreath.flip]

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates

namespace CFSG.Quasithin.Chapter15.Section02
open Section01 ChapterD ChapterD.UniqueFactor SmallActionsSource
open Representation NoncentralChiefRefinement Stellmacher Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Source marked factors on the original pair of chief intervals: their
planes are the actual commutators, one element of the specified Sylow subgroup
interchanges both pairs, and either marked residual normally generates O²(H). -/
theorem ChosenSmallSource.two_chief_marked_geometry
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ s : SeriesOn U, ∃ (i j : Fin s.series.length), i ≠ j ∧
      ¬ s.Central i ∧ ¬ s.Central j ∧
      ∃ (c : ChiefWreathCoordinates (s.factorRepresentation i))
        (d : ChiefWreathCoordinates (s.factorRepresentation j)) (k : ChiefWreath.C2),
        c.actor.ker = pCore 2 H ∧ d.actor.ker = pCore 2 H ∧
        c.factor 1 = d.factor k ∧
        c.factor ChiefWreath.flip = d.factor (ChiefWreath.flip*k) ∧
        (letI := BinaryGroupAction.action (s.factorRepresentation i)
          ∀ l, commutatorAction (c.factor l) (Multiplicative (Additive (s.Factor i))) = c.plane l) ∧
        (letI := BinaryGroupAction.action (s.factorRepresentation j)
          ∀ l, commutatorAction (d.factor l) (Multiplicative (Additive (s.Factor j))) = d.plane l) ∧
        (∀ l, ChosenGeometry.residual H =
          conjugateSpanBy ((c.residualFactor l).map H.subtype) H) ∧
        ∃ t : H, (t : G)∈(T : Subgroup G) ∧
          (c.actor t)^2=1 ∧ (c.actor t).right=ChiefWreath.flip ∧
          (d.actor t)^2=1 ∧ (d.actor t).right=ChiefWreath.flip ∧
          (∀ l, (c.factor l).map (MulAut.conj t).toMonoidHom = c.factor (ChiefWreath.flip*l)) ∧
          (∀ l, (d.factor l).map (MulAut.conj t).toMonoidHom = d.factor (ChiefWreath.flip*l)) ∧
          (letI := BinaryGroupAction.action (s.factorRepresentation i)
            ∀ l, (c.plane l).map (MulDistribMulAction.toMulAut H _ t).toMonoidHom =
              c.plane (ChiefWreath.flip*l)) ∧
          (letI := BinaryGroupAction.action (s.factorRepresentation j)
            ∀ l, (d.plane l).map (MulDistribMulAction.toMulAut H _ t).toMonoidHom =
              d.plane (ChiefWreath.flip*l)) := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s
  obtain ⟨i,j,hij,hi,hj,c,d,hc,hd,hb⟩ := h.two_chief_coordinates_with_common_base hunique hH he s
  obtain ⟨k,hk,hk'⟩ := c.factors_align d (hc.trans hd.symm) hb
  refine ⟨i,j,hij,hi,hj,c,d,k,hc,hd,hk,hk',c.factor_support,d.factor_support,?_,?_⟩
  · intro l
    have hh := congrArg (Subgroup.map H.subtype) (c.residualFactor_span l)
    rw [map_conjugateSpanBy,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm
  · obtain ⟨t,ht,ht2,htr,htf,htp⟩ := c.sylow_interchange (T.subtype hH.1.1.2)
    have hdt : (d.actor t).right=ChiefWreath.flip := (c.right_eq_of_common_base d hb t).symm.trans htr
    have hdt2 : (d.actor t)^2=1 := by
      rw [←map_pow]
      have hh : t^2∈c.actor.ker := by change c.actor (t^2)=1; rwa [map_pow]
      exact show t^2∈d.actor.ker from (hc.trans hd.symm) ▸ hh
    refine ⟨t,ht,ht2,htr,hdt2,hdt,htf,?_,htp,?_⟩
    · intro l
      rw [d.factor_conj,hdt]
    · let := BinaryGroupAction.action (s.factorRepresentation j)
      intro l
      rw [d.plane_conj,hdt]

end CFSG.Quasithin.Chapter15.Section02

open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 ChapterD ChapterD.UniqueFactor SmallActionsSource ChosenGeometry

private theorem two_base_card (E : Subgroup ChiefWreathActor) (hp : IsPGroup 2 E)
    (hb : E≤ChiefWreath.base) : Nat.card E ∣ 4 := by
  have hd := Subgroup.card_dvd_of_le hb
  rw [ChiefWreath.base_card] at hd
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  rw [hn] at hd ⊢
  have hc : Nat.Coprime (2^n) 9 := (by decide : Nat.Coprime 2 9).pow_left n
  exact hc.dvd_of_dvd_mul_right (show 2^n ∣ 4*9 from hd)

variable {G : Type*} [Group G] [Finite G]
/-- Every original minimal offender has image of order two or four in the
actual two-core quotient. The order-four case is the remaining source exclusion. -/
theorem ChosenSmallSource.delta_image_card_two_or_four
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hA : A∈delta H) :
    Nat.card (offenderImage H A)=2 ∨ Nat.card (offenderImage H A)=4 := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hi,hj,c,d,hc,hd,hb⟩ := h.two_chief_coordinates_with_common_base hunique hH he s
  let A₀ := A.subgroupOf H
  let : IsElementaryAbelian 2 A := hA.1.2.1
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hA.1.1
  have hAm : A₀ ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup H) := by
    apply (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ A₀).mp
    simpa only [A₀,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hA.1.1] using hA.1
  have hAb : A₀ ≤ ChiefWreath.base.comap c.actor := by
    rw [←c.factor_sup_eq_base,h.chief_marked_base hunique hH he s i hi c]
    exact le_sup_of_le_left (le_sSup hAm)
  let E := A₀.map c.actor
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map c.actor
  have hcard : Nat.card E=Nat.card (offenderImage H A) := by
    change Nat.card (A₀.map c.actor)=Nat.card (A₀.map (QuotientGroup.mk' (pCore 2 H)))
    rw [←Subgroup.relIndex_ker,←Subgroup.relIndex_ker,hc,QuotientGroup.ker_mk']
  have hdiv := two_base_card E (IsElementaryAbelian.isPGroup 2 E) (map_le_iff_le_comap.mpr hAb)
  rw [hcard] at hdiv
  have hne : Nat.card (offenderImage H A)≠1 := by
    intro hh
    have hbot := Subgroup.card_eq_one.mp hh
    have hle := (map_eq_bot_iff (A.subgroupOf H)).mp hbot
    rw [QuotientGroup.ker_mk'] at hle
    have hm := map_mono (f:=H.subtype) hle
    rw [map_subgroupOf_eq_of_le hA.1.1] at hm
    exact hA.2.1 hm
  obtain ⟨n,hn,heq⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
    (show Nat.card (offenderImage H A) ∣ 2^2 from hdiv)
  interval_cases n
  · exact (hne (by simpa using heq)).elim
  · exact Or.inl (by simpa using heq)
  · exact Or.inr (by simpa using heq)
end CFSG.Quasithin.Chapter15.Section02
