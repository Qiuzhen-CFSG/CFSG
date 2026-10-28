module
public import Theory.SpecificGroups.BinaryLinear.FirstNodeParabolic
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Orders
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual
public import Theory.GroupTheory.PResidual.PerfectCover
/-!
# Residual size of the binary four-space endpoint

The two-space stabilizer has order 576. Its two-core quotient is the
literal S₃ × S₃, whose two-residual has order nine. Sixteen distinct root
rectangles lie in the kernel of the residual quotient map, so the original
residual has at least 144 elements. The calculation retains the supplied
basis and uses symbolic root formulas rather than group enumeration.

Source: Aschbacher--Smith 15.1.22(3), printed pp.1099--1100. The constrained
application must additionally use the nontrivial original two-core; this
model bound alone does not exclude an A₃ product.
-/
public section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic OrderedResidualConjugators SmallParabolicLevi
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
private noncomputable def rootChoice {m : ℕ} (b : Basis m)
    (r s : Fin (m+1)) (hrs : r ≠ s) (a : ZMod 2) : LinearGroup (m+1) :=
  if a = 0 then 1 else root b r s hrs

private theorem rootChoice_apply {m : ℕ} (b : Basis m)
    (r s : Fin (m+1)) (hrs : r ≠ s) (a : ZMod 2) (v : Space (m+1)) :
    rootChoice b r s hrs a v = v + (a * b.coord s v) • b r := by
  have hroot : root b r s hrs v = v + b.coord s v • b r := by
    have he : root b r s hrs = transvection (b r) (b.coord s) (by simp [hrs]) := by
      apply b.ext'
      intro j
      rw [root_basis]
      change (if j = s then b j + b r else b j) = b j + b.coord s (b j) • b r
      by_cases hj : j = s <;> simp [hj,Module.Basis.coord_apply]
    rw [he]
    rfl
  by_cases ha : a = 0
  · simp [rootChoice,ha]
  · have ha1 : a = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x=1) _ ha
    simp [rootChoice,ha1,hroot]

private noncomputable def rootRectangle {m : ℕ} (hm : 3 ≤ m) (b : Basis m)
    (a : Fin 2 → Fin 2 → ZMod 2) : LinearGroup (m+1) :=
  rootChoice b ⟨0,by omega⟩ ⟨2,by omega⟩ (by simp) (a 0 0) *
  rootChoice b ⟨0,by omega⟩ ⟨3,by omega⟩ (by simp) (a 0 1) *
  rootChoice b ⟨1,by omega⟩ ⟨2,by omega⟩ (by simp) (a 1 0) *
  rootChoice b ⟨1,by omega⟩ ⟨3,by omega⟩ (by simp) (a 1 1)

private theorem rootRectangle_entry {m : ℕ} (hm : 3 ≤ m) (b : Basis m)
    (a : Fin 2 → Fin 2 → ZMod 2) (i j : Fin 2) :
    b.coord ⟨i.val,by omega⟩ (rootRectangle hm b a (b ⟨j.val+2,by omega⟩)) = a i j := by
  fin_cases i <;> fin_cases j <;>
    simp [rootRectangle,LinearEquiv.mul_apply,rootChoice_apply,map_add,map_smul,
      Module.Basis.coord_apply]

private theorem root_in_radical {m : ℕ} (b : Basis m) (i : Fin m)
    (r s : Fin (m+1)) (hrs : r ≠ s) (hr : r.val ≤ i.val) (hs : i.val < s.val) :
    root b r s hrs ∈ radical (cutSpace b i) := by
  have hcoord : ∀ v ∈ cutSpace b i, b.coord s v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j,hj,rfl⟩ := hv
      have hjs : j ≠ s := by intro he; subst j; exact (Nat.not_le_of_gt hs) hj
      simp [Module.Basis.coord_apply,hjs]
    | zero => exact map_zero _
    | add v w hv hw ihv ihw => simp only [map_add,ihv,ihw,add_zero]
    | smul c v hv ih => simp only [map_smul,ih,smul_zero]
  have he : root b r s hrs = transvection (b r) (b.coord s) (by simp [hrs]) := by
    apply b.ext'
    intro j
    rw [root_basis]
    change (if j = s then b j + b r else b j) = b j + b.coord s (b j) • b r
    by_cases hj : j = s <;> simp [hj,Module.Basis.coord_apply]
  rw [he]
  constructor
  · intro v hv
    change v + b.coord s v • b r = v
    rw [hcoord v hv,zero_smul,add_zero]
  · intro v
    change v + b.coord s v • b r - v ∈ cutSpace b i
    rw [add_sub_cancel_left]
    exact (cutSpace b i).smul_mem _ ((basis_mem_cutSpace b i r).mpr hr)


/-- The actual endpoint order and the lower bound for its two-residual. -/
theorem four_endpoint_residual_data (b : Basis 3) :
    Nat.card (parabolic (cutSpace b 1)) = 576 ∧
      144 ≤ Nat.card (pResidual 2 (parabolic (cutSpace b 1))) := by
  let W := cutSpace b (1 : Fin 3)
  let E := parabolic W
  let R := pResidual 2 E
  let q := QuotientGroup.mk' (pCore 2 E)
  let f := q.subgroupMap R
  have hW : Module.finrank (ZMod 2) W = 2 := cutSpace_finrank b 1
  have hQ : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 2 := by
    have hh := W.finrank_quotient_add_finrank
    rw [hW] at hh
    simp [Space] at hh
    omega
  let a : W ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hW)
  let c : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hQ)
  let e := (quotientTwoCoreEquivOfCoordinates W a c).trans
    (linearTwoEquivSymmetricThree.prodCongr linearTwoEquivSymmetricThree)
  have him : Nat.card (R.map q) = 9 := by
    rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
    have hh := congrArg (fun D : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) => Nat.card D)
      (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective)
    rw [card_map_of_injective e.injective,SymmetricThreeProductResidual.residual_card] at hh
    exact hh
  have hn : minimalParabolic b 0 ≤ E := by
    intro g hg
    exact (mem_cutStabilizer b {0}ᶜ g).mp hg 1 (by decide)
  have hr : nodeResidual b 0 ≤ R.map E.subtype := embedded_pResidual_mono 2 hn
  have hmem (v : Fin 2 → Fin 2 → ZMod 2) :
      rootRectangle (by decide : 3 ≤ 3) b v ∈ R.map E.subtype ⊓ radical W := by
    have hroot (i j : Fin 4) (hij : i ≠ j) (hi : i.val=0 ∨ i.val=1) (hj : 1 < j.val)
        (c : ZMod 2) : rootChoice b i j hij c ∈ R.map E.subtype ⊓ radical W := by
      unfold rootChoice
      split
      · exact one_mem _
      · exact ⟨hr (incident_root_mem_nodeResidual b 0 i j hij
          (.inr ⟨hi.imp (fun he => Fin.ext he) (fun he => Fin.ext he),hj⟩)),
          root_in_radical b 1 i j hij (by rcases hi with hi | hi <;> simp [hi]) hj⟩
    apply mul_mem
    · apply mul_mem
      · apply mul_mem <;> apply hroot <;> simp
      · apply hroot <;> simp
    · apply hroot <;> simp
  have h16 : 16 ≤ Nat.card f.ker := by
    have hh (v : Fin 2 → Fin 2 → ZMod 2) :
        ∃ x : f.ker, ((x : R) : LinearGroup 4) = rootRectangle (by decide) b v := by
      obtain ⟨x,hx,he⟩ := (hmem v).1
      have hxQ : x ∈ pCore 2 E := by
        have hz := (hmem v).2
        rw [←map_twoCore_eq_radical W] at hz
        obtain ⟨z,hz,hze⟩ := hz
        have hzx : z = x := Subtype.ext (hze.trans he.symm)
        exact hzx ▸ hz
      refine ⟨⟨⟨x,hx⟩,?_⟩,he⟩
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr hxQ
    choose u hu using hh
    have hinj : Function.Injective u := by
      intro v w he
      ext i j
      have hvw := (hu v).symm.trans ((congrArg (fun x : f.ker => ((x : R) : LinearGroup 4)) he).trans (hu w))
      have hv := congrArg (fun g : LinearGroup 4 => b.coord ⟨i.val,by omega⟩ (g (b ⟨j.val+2,by omega⟩))) hvw
      exact (rootRectangle_entry (by decide) b v i j).symm.trans
        (hv.trans (rootRectangle_entry (by decide) b w i j))
    simpa [Nat.card_fun,Nat.card_fin,Nat.card_zmod] using Nat.card_le_card_of_injective u hinj
  have hc := f.ker.card_mul_index
  rw [index_ker,f.range_eq_top_of_surjective (q.subgroupMap_surjective R),card_top,him] at hc
  refine ⟨FourParabolicAction.twoSpace_parabolic_card W (by simp [Space]) hW,?_⟩
  change 144 ≤ Nat.card R
  omega
end BinaryLinear.InvariantNodeActions
