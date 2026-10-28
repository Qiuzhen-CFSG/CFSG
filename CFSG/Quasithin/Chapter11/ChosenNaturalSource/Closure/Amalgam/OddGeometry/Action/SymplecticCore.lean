module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action.Core
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic

/-!
# The symplectic odd-pair core intersections

Keep U = ⟨V^(KT)⟩ distinct from J = ⟨V₃^(KT)⟩. Point-radical coordinates
bound [J,O₂(KT)] by V₁. A radical element moving V₃ has a displacement
map onto the field, so it cannot fix a subgroup of index at most two when
q > 2. This rigidity propagates to J. Elements of O₂(KT) fixing J move
U only into V₁, by the central-root calculation and conjugate generation.

Apply these facts in both orientations. Disjointness of V₁ and V₁ᵍ first
makes the intersections with J and Jᵍ commute. Rigidity extends this
centralization, and the central-root bounds then make U₁ and U₀ commute.
The resulting bound feeds the original OddPair in SymplecticPair.lean;
it does not assert the stronger full-core displacement bound used for SL₃.
Source: Aschbacher--Smith, 11.5.8, printed p.784.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
variable {G : Type*} [Group G]

theorem map_unmap (W : Subgroup G) (e : G ≃* G) :
    (W.map e.toMonoidHom).map e.symm.toMonoidHom = W :=
  (map_symm_eq_iff_map_eq W).mpr rfl

theorem unmap_map (W : Subgroup G) (e : G ≃* G) :
    (W.map e.symm.toMonoidHom).map e.toMonoidHom = W :=
  map_unmap W e.symm

theorem map_centralizer (W : Subgroup G) (e : G ≃* G) :
    (centralizer (W : Set G)).map e.toMonoidHom =
      centralizer (W.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

-- Fixing a subgroup of index at most two forces fixation of the whole module.
def IndexRigid (W Q : Subgroup G) : Prop :=
  ∀ B A : Subgroup G, B.relIndex W ≤ 2 → A ≤ Q →
    B ⊓ W ≤ centralizer (A : Set G) → W ≤ centralizer (A : Set G)

theorem rigid_map (W Q : Subgroup G) (hr : IndexRigid W Q) (e : G ≃* G) :
    IndexRigid (W.map e.toMonoidHom) (Q.map e.toMonoidHom) := by
  intro B A hi hA hc
  let B' := B.map e.symm.toMonoidHom
  let A' := A.map e.symm.toMonoidHom
  have hB : B'.relIndex W ≤ 2 := by
    have hh := relIndex_map_map_of_injective (f := e.symm.toMonoidHom) B (W.map e.toMonoidHom) e.symm.injective
    simpa only [map_unmap] using hh.le.trans hi
  have hAQ : A' ≤ Q := by
    have hh := map_mono (f := e.symm.toMonoidHom) hA
    simpa only [map_unmap] using hh
  have hc' : B' ⊓ W ≤ centralizer (A' : Set G) := by
    have hh := map_mono (f := e.symm.toMonoidHom) hc
    rw [map_inf _ _ _ e.symm.injective] at hh
    simpa only [map_unmap, map_centralizer] using hh
  have hh := map_mono (f := e.toMonoidHom) (hr B' A' hB hAQ hc')
  simpa only [A', map_centralizer, unmap_map] using hh

variable [Finite G]

theorem rigid_span (W Q H : Subgroup G) (hr : IndexRigid W Q)
    (hQ : H ≤ normalizer (Q : Set G)) : IndexRigid (conjugateSpanBy W H) Q := by
  intro B A hi hA hc
  rw [conjugateSpanBy_eq_iSup_conj]
  apply iSup_le
  intro k
  have hW : W.map (MulAut.conj (k : G)).toMonoidHom ≤ conjugateSpanBy W H := by
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : H => W.map (MulAut.conj (k : G)).toMonoidHom) k
  have hh := rigid_map W Q hr (MulAut.conj (k : G))
  have he : Q.map (MulAut.conj (k : G)).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (hQ k.property)
  exact hh B A ((B.relIndex_le_of_le_right hW (by exact index_ne_zero_of_finite)).trans hi)
    (hA.trans he.ge) ((inf_le_inf_left _ hW).trans hc)

/-- Two transverse index-two core intersections commute once fixation on each
hyperplane closure extends across index two, and hyperplane fixers move only
the point on the corresponding full closure. -/
theorem transverse_core_commutator
    (U Q Z J U' Q' Z' J' : Subgroup G)
    (hJ : J ≤ U) (hJ' : J' ≤ U')
    (hr : IndexRigid J Q) (hr' : IndexRigid J' Q')
    (hc : ⁅J,Q⁆ ≤ Z) (hc' : ⁅J',Q'⁆ ≤ Z')
    (hz : ⁅U,Q ⊓ centralizer (J : Set G)⁆ ≤ Z)
    (hz' : ⁅U',Q' ⊓ centralizer (J' : Set G)⁆ ≤ Z')
    (hi : (U ⊓ Q').relIndex U ≤ 2) (hi' : (U' ⊓ Q).relIndex U' ≤ 2)
    (hdis : Z ⊓ Z' = ⊥) : ⁅U ⊓ Q',U' ⊓ Q⁆ = ⊥ := by
  let B := U ⊓ Q'
  let B' := U' ⊓ Q
  have hBJ : B.relIndex J ≤ 2 :=
    (B.relIndex_le_of_le_right hJ (by exact index_ne_zero_of_finite)).trans hi
  have hBJ' : B'.relIndex J' ≤ 2 :=
    (B'.relIndex_le_of_le_right hJ' (by exact index_ne_zero_of_finite)).trans hi'
  have h0 : ⁅B ⊓ J,B' ⊓ J'⁆ = ⊥ := by
    apply bot_unique
    rw [← hdis]
    apply le_inf
    · exact (commutator_mono inf_le_right (inf_le_left.trans inf_le_right)).trans hc
    · rw [commutator_comm]
      exact (commutator_mono inf_le_right (inf_le_left.trans inf_le_right)).trans hc'
  have h1 : J ≤ centralizer ((B' ⊓ J' : Subgroup G) : Set G) :=
    hr B (B' ⊓ J') hBJ (inf_le_left.trans inf_le_right)
      (commutator_eq_bot_iff_le_centralizer.mp h0)
  have h2 : ⁅B,B' ⊓ J'⁆ = ⊥ := by
    apply bot_unique
    rw [← hdis]
    apply le_inf
    · exact (commutator_mono inf_le_left
        (le_inf (inf_le_left.trans inf_le_right) (le_centralizer_iff.mp h1))).trans hz
    · rw [commutator_comm]
      exact (commutator_mono inf_le_right inf_le_right).trans hc'
  have h3 : J' ≤ centralizer (B : Set G) :=
    hr' B' B hBJ' inf_le_right
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h2))
  have h4 : ⁅B,U'⁆ ≤ Z' := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (le_inf inf_le_right (le_centralizer_iff.mp h3))).trans hz'
  have h5 : ⁅B ⊓ J,B'⁆ = ⊥ := by
    apply bot_unique
    rw [← hdis]
    exact le_inf ((commutator_mono inf_le_right inf_le_right).trans hc)
      ((commutator_mono inf_le_left inf_le_left).trans h4)
  have h6 : J ≤ centralizer (B' : Set G) :=
    hr B B' hBJ inf_le_right (commutator_eq_bot_iff_le_centralizer.mp h5)
  apply bot_unique
  rw [← hdis]
  exact le_inf ((commutator_mono inf_le_left
    (le_inf inf_le_right (le_centralizer_iff.mp h6))).trans hz)
    ((commutator_mono le_rfl inf_le_left).trans h4)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action


set_option backward.isDefEq.respectTransparency false

open Subgroup
open scoped IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
open Chapter12.Section02 Closure.Symplectic Closure.Symplectic.Terminal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

public theorem hyperplane_rigidity (m : MarkedFlag E) (p : PointCoordinates E m)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (B A : Subgroup G) (hA : A ≤ E.R₁) (hi : B.relIndex E.V₃ ≤ 2)
    (hC : A ≤ centralizer ((B ⊓ E.V₃ : Subgroup G) : Set G)) :
    A ≤ centralizer (E.V₃ : Set G) := by
  let π := markedProjection E m p.basis
  have hinj := markedProjection_injective E m p.basis hc
  intro a ha
  let aN : normalizer (V : Set G) := ⟨a, radical_normalizes_seed E (hA ha)⟩
  obtain ⟨u,v,z,hr⟩ := p.radical ⟨a,hA ha⟩
  have huv : u = 0 ∧ v = 0 := by
    by_contra! hn
    have hn' : u ≠ 0 ∨ v ≠ 0 := by tauto
    let δ : E.V₃ →* Multiplicative E.input.field.Carrier :=
      { toFun := fun x => Multiplicative.ofAdd
          (u * (π ⟨x.val,D.centralQuotientPreimage_le _ x.property⟩).toAdd (.inr 1) +
           v * (π ⟨x.val,D.centralQuotientPreimage_le _ x.property⟩).toAdd (.inl 1))
        map_one' := by
          change Multiplicative.ofAdd (u * (π 1).toAdd (.inr 1) +
            v * (π 1).toAdd (.inl 1)) = 1
          simp
        map_mul' := by
          intro x y
          change Multiplicative.ofAdd _ = Multiplicative.ofAdd _
          apply congrArg Multiplicative.ofAdd
          have hxy : (⟨(x*y).val,D.centralQuotientPreimage_le _ (x*y).property⟩ : V) =
              (⟨x.val,D.centralQuotientPreimage_le _ x.property⟩ : V) *
                ⟨y.val,D.centralQuotientPreimage_le _ y.property⟩ := rfl
          simp only [hxy,map_mul,toAdd_mul,toAdd_ofAdd,Pi.add_apply]
          ring }
    have hsurj : Function.Surjective δ := by
      intro t
      rcases hn' with hu | hv
      · obtain ⟨y,hy⟩ := markedProjection_surjective E m p.basis
          (Multiplicative.ofAdd (Pi.single (.inr 1) (t.toAdd / u)))
        change π y = _ at hy
        have hy3 : (y : G) ∈ E.V₃ := (p.three y).mpr (by
          change (π y).toAdd (.inr 0) = 0
          rw [hy]
          simp)
        refine ⟨⟨y,hy3⟩, ?_⟩
        change Multiplicative.ofAdd _ = t
        apply Multiplicative.toAdd.injective
        simp [hy,hu,mul_div_cancel₀]
      · obtain ⟨y,hy⟩ := markedProjection_surjective E m p.basis
          (Multiplicative.ofAdd (Pi.single (.inl 1) (t.toAdd / v)))
        change π y = _ at hy
        have hy3 : (y : G) ∈ E.V₃ := (p.three y).mpr (by
          change (π y).toAdd (.inr 0) = 0
          rw [hy]
          simp)
        refine ⟨⟨y,hy3⟩, ?_⟩
        change Multiplicative.ofAdd _ = t
        apply Multiplicative.toAdd.injective
        simp [hy,hv,mul_div_cancel₀]
    have hker : B.subgroupOf E.V₃ ≤ δ.ker := by
      intro x hx
      let xV : V := ⟨x.val,D.centralQuotientPreimage_le _ x.property⟩
      have hfix : V.normalizerMonoidHom aN xV = xV := by
        apply Subtype.ext
        change a*x.val*a⁻¹=x.val
        rw [← hC ha x.val ⟨hx,x.property⟩,mul_inv_cancel_right]
      have he := congrFun (hr xV) (.inl 0)
      rw [hfix,PlaneModel.radical_apply] at he
      have hx3 := (p.three xV).mp x.property
      change δ x = 1
      apply Multiplicative.toAdd.injective
      change u * (π xV).toAdd (.inr 1) + v * (π xV).toAdd (.inl 1) = 0
      change (π xV).toAdd (.inl 0) = _ at he
      change (π xV).toAdd (.inr 0) = 0 at hx3
      change (π xV).toAdd (.inl 0) = (π xV).toAdd (.inl 0) +
        v * (π xV).toAdd (.inl 1) + z * (π xV).toAdd (.inr 0) +
          u * (π xV).toAdd (.inr 1) at he
      rw [hx3,mul_zero,add_zero] at he
      linear_combination -he
    have hidx : δ.ker.index ≤ 2 :=
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (index_ne_zero_of_finite))
        (index_dvd_of_le hker)).trans hi
    rw [index_ker,δ.range_eq_top.mpr hsurj,card_top] at hidx
    change Nat.card E.input.field.Carrier ≤ 2 at hidx
    rw [E.input.field.card_eq] at hidx
    have hfour : 4 ≤ 2 ^ E.input.field.degree := by
      change (2 : ℕ)^2 ≤ 2 ^ E.input.field.degree
      exact Nat.pow_le_pow_right (by decide) (by have := E.input.nonbinary; omega)
    omega
  intro x hx
  let xV : V := ⟨x,D.centralQuotientPreimage_le _ hx⟩
  have he : V.normalizerMonoidHom aN xV = xV := by
    apply hinj
    apply Multiplicative.toAdd.injective
    rw [hr,huv.1,huv.2]
    exact PlaneModel.central_fixes_three z _ ((p.three xV).mp hx)
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action


open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
open Chapter12.Section02 Closure.Symplectic Closure.Symplectic.Terminal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

noncomputable def hyperplaneClosure : Subgroup G := conjugateSpanBy E.V₃ (KT E)

theorem span_commutator_bound (A B : Subgroup G) (h : LocalInputs E)
    (hA : A ≤ KT E) (hB : KT E ≤ normalizer (B : Set G))
    (hc : ⁅A,B⁆ ≤ E.V₁) : ⁅conjugateSpanBy A (KT E),B⁆ ≤ E.V₁ := by
  have hHZ : KT E ≤ normalizer (E.V₁ : Set G) := KT_le_G₁ E h
  have hs : conjugateSpanBy A (KT E) ≤ commutatorPreimage (KT E) B E.V₁ :=
    conjugateSpanBy_le (le_commutatorPreimage hA hc)
      (commutatorPreimage_normalized _ _ _ _ hHZ (KT E).le_normalizer hB hHZ)
  exact (commutator_mono hs le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hHZ)

theorem hyperplane_closure_core_bound (m : MarkedFlag E) (p : PointCoordinates E m)
    (h : LocalInputs E) : ⁅hyperplaneClosure E,(KT E).pCoreIn 2⁆ ≤ E.V₁ := by
  apply span_commutator_bound E E.V₃ _ h
    ((D.centralQuotientPreimage_le E.threeSpace).trans (V_le_KT E))
    ((KT E).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact Even.Symplectic.threeSpace_commutator_le_point m p _ (core_le_radical E)

theorem hyperplane_fixer_closure_bound (m : MarkedFlag E) (p : PointCoordinates E m)
    (h : LocalInputs E) :
    ⁅localClosure E,(KT E).pCoreIn 2 ⊓ centralizer (hyperplaneClosure E : Set G)⁆ ≤ E.V₁ := by
  apply span_commutator_bound E V _ h (V_le_KT E)
  · exact (le_inf
      ((KT E).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
      ((le_normalizer_conjugateSpanBy E.V₃ (KT E)).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  · exact p.commutator_le_point _ (inf_le_left.trans (core_le_radical E))
      (inf_le_right.trans (centralizer_le (le_conjugateSpanBy E.V₃ (KT E))))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
open Subgroup Chapter12.Section02 Closure.Symplectic Closure.Symplectic.Terminal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

theorem hyperplane_closure_rigid (m : MarkedFlag E) (p : PointCoordinates E m)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    IndexRigid (hyperplaneClosure E) ((KT E).pCoreIn 2) := by
  apply rigid_span E.V₃ ((KT E).pCoreIn 2) (KT E) _
    ((KT E).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  intro B A hi hA hc
  exact le_centralizer_iff.mp (hyperplane_rigidity E m p hfixed B A
    (hA.trans (core_le_radical E)) hi (le_centralizer_iff.mp hc))

public theorem symplectic_core_intersections_commute
    (m : MarkedFlag E) (p : PointCoordinates E m)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (h : LocalInputs E) (g : G)
    (hi : (U₁ E g).relIndex (localClosure E) ≤ 2)
    (hi' : (U₀ E g).relIndex ((localClosure E).map (MulAut.conj g).toMonoidHom) ≤ 2)
    (hdis : E.V₁ ⊓ E.V₁.map (MulAut.conj g).toMonoidHom = ⊥) :
    ⁅U₁ E g,U₀ E g⁆ = ⊥ := by
  let e := MulAut.conj g
  let U := localClosure E
  let Q := (KT E).pCoreIn 2
  let J := hyperplaneClosure E
  have hJ : J ≤ U := conjugateSpanBy_mono (D.centralQuotientPreimage_le _) le_rfl
  have hr := hyperplane_closure_rigid E m p hfixed
  have hc := hyperplane_closure_core_bound E m p h
  have hz := hyperplane_fixer_closure_bound E m p h
  have hc' := map_mono (f := e.toMonoidHom) hc
  rw [map_commutator] at hc'
  have hz' := map_mono (f := e.toMonoidHom) hz
  rw [map_commutator,map_inf _ _ _ e.injective,map_centralizer] at hz'
  have hQ : ((KT E).map e.toMonoidHom).pCoreIn 2 = Q.map e.toMonoidHom :=
    Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 e.toMonoidHom e.injective (KT E)
  have hi0 : (U ⊓ Q.map e.toMonoidHom).relIndex U ≤ 2 := by
    change (U ⊓ ((KT E).map e.toMonoidHom).pCoreIn 2).relIndex U ≤ 2 at hi
    rwa [hQ] at hi
  have hh := transverse_core_commutator U Q E.V₁ J
    (U.map e.toMonoidHom) (Q.map e.toMonoidHom) (E.V₁.map e.toMonoidHom)
    (J.map e.toMonoidHom) hJ (map_mono hJ) hr (rigid_map J Q hr e)
    hc hc' hz hz' hi0 hi' hdis
  change ⁅U ⊓ ((KT E).map e.toMonoidHom).pCoreIn 2,U.map e.toMonoidHom ⊓ Q⁆ = ⊥
  rw [hQ]
  exact hh


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
