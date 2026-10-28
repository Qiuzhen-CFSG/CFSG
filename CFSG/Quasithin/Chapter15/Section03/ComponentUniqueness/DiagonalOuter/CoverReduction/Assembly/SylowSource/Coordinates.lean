module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.SylowSource
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The natural-coordinate signs on the two source cubic factors

A faithful dihedral quarter-turn interchanges the two natural planes. Conjugating
its distinguished plane-fixing reflection therefore fixes the opposite plane.
Actors supported on opposite planes commute modulo the actual natural kernel;
this gives the component-fixing and opposite-inverting signs of the graph
reflection for every compatible coordinate choice.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.SylowNormalizer
open scoped Pointwise

private theorem plane_actor_card : Nat.card OrthogonalPlaneActor = 6 := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  rw [Nat.card_congr e.toEquiv]
  norm_num [Nat.card_perm, Fintype.card_perm]

private theorem base_sixth_power (x : OrthogonalActor) (h : x.right = 1) : x ^ 6 = 1 := by
  have hp : ∀ n : ℕ, (x^n).right = 1 ∧ ∀ i, (x^n).left i = (x.left i)^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      constructor
      · simp only [pow_succ, RegularWreathProduct.mul_right, ih.1, h, one_mul]
      · intro i
        simp only [pow_succ, RegularWreathProduct.mul_left, Pi.mul_apply, ih.1,
          inv_one, one_mul, ih.2]
  apply RegularWreathProduct.ext (funext fun i => ?_) (hp 6).1
  rw [(hp 6).2]
  change (x.left i)^6=1
  simpa only [plane_actor_card] using (pow_card_eq_one' :
    (x.left i)^Nat.card OrthogonalPlaneActor = 1)

/-- Every faithful dihedral model has an actual plane-swapping quarter-turn. -/
theorem faithful_dihedral_rotation_swaps (e : DihedralGroup 4 →* OrthogonalActor)
    (he : Function.Injective e) : (e (.r 1)).right ≠ 1 := by
  intro hr
  have h6 : (DihedralGroup.r (1 : ZMod 4))^6=1 := he (by
    rw [map_pow, base_sixth_power _ hr, map_one])
  have hd := orderOf_dvd_of_pow_eq_one h6
  rw [DihedralGroup.orderOf_r_one] at hd
  norm_num at hd


open LocalCover LocalCover.SourceBorel Assembly
variable {G : Type*} [Group G] [Finite G]

/-- The other reflection fixes the opposite source plane for every compatible
coordinate choice; no preferred dihedral embedding is used. -/
theorem source_first_fixes_second {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (r : LocalResult d I L)
    (a : NaturalOrthogonalAction d.M d.V) (hYSM : d.Y ⊔ d.S ≤ d.M)
    (hplane : a.plane 1 = r.cover.borel.W₁)
    (c : NaturalCoordinates d.T d.M d.Y d.S (d.Y.pCoreIn 2) d.V r.cover.borel.W₁
      a d.sylow_le hYSM)
    (t : d.T) (ht : c.tProjection t = .sr 0) :
    (t : G) ∈ centralizer (r.cover.borel.W₂ : Set G) := by
  obtain ⟨u, hu⟩ := c.tOnto (.r 1)
  have hswap : (a.actor (inclusion d.sylow_le u)).right ≠ 1 := by
    rw [c.tCompatible, hu]
    exact faithful_dihedral_rotation_swaps c.tEmbedding c.tInjective
  have hun : (u : G) ∉ normalizer (r.cover.borel.W₁ : Set G) := by
    rw [← hplane]
    change ((inclusion d.sylow_le u : d.M) : G) ∉ normalizer (a.plane 1 : Set G)
    rw [cyclic_mem_plane_normalizer_iff a (inclusion d.sylow_le u) 1]
    exact hswap
  have humap : r.cover.borel.W₁.map (MulAut.conj (u : G)).toMonoidHom =
      r.cover.borel.W₂ := by
    have hidx (i : OrthogonalPlaneIndex) (hi : i ≠ 1) :
        i = Multiplicative.ofAdd (1 : ZMod 2) := by
      revert i
      decide +kernel
    rcases r.cover.borel.planes with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · have hr : (d.action.actor (inclusion d.sylow_le u)).right ≠ 1 := by
        rw [h₁] at hun
        change ((inclusion d.sylow_le u : d.M) : G) ∉ normalizer (d.action.plane 1 : Set G) at hun
        rwa [cyclic_mem_plane_normalizer_iff d.action (inclusion d.sylow_le u) 1] at hun
      rw [h₁,h₂]
      change (d.action.plane 1).map (MulAut.conj ((inclusion d.sylow_le u : d.M) : G)).toMonoidHom = d.action.plane (Multiplicative.ofAdd (1 : ZMod 2))
      rw [cyclic_plane_map d.action (inclusion d.sylow_le u),hidx _ hr,mul_one]
    · have hr : (d.action.actor (inclusion d.sylow_le u)).right ≠ 1 := by
        rw [h₁] at hun
        change ((inclusion d.sylow_le u : d.M) : G) ∉ normalizer (d.action.plane (Multiplicative.ofAdd (1 : ZMod 2)) : Set G) at hun
        rwa [cyclic_mem_plane_normalizer_iff d.action (inclusion d.sylow_le u)
          (Multiplicative.ofAdd (1 : ZMod 2))] at hun
      rw [h₁,h₂]
      change (d.action.plane (Multiplicative.ofAdd (1 : ZMod 2))).map (MulAut.conj ((inclusion d.sylow_le u : d.M) : G)).toMonoidHom = d.action.plane 1
      rw [cyclic_plane_map d.action (inclusion d.sylow_le u),hidx _ hr]
      rfl
  let k : d.T := u⁻¹*t*u
  have hk : c.tProjection k = .sr 2 := by
    simp only [k,map_mul,map_inv,hu,ht]
    decide
  have hfix := c.fixes_plane k hk
  have hm : (MulAut.conj (u : G)) (k : G) ∈
      centralizer ((r.cover.borel.W₁.map (MulAut.conj (u : G)).toMonoidHom) : Set G) :=
    map_centralizer_le_centralizer_image _ _ (mem_map_of_mem _ hfix)
  rw [humap] at hm
  convert hm using 1
  change (t : G) = (u : G) * ((u : G)⁻¹ * (t : G) * (u : G)) * (u : G)⁻¹
  group

/-- Actors supported on opposite source planes commute modulo the actual two-core. -/
theorem source_cross_plane_commutator {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) {x y : G}
    (hx : x ∈ d.Y ⊔ d.S) (hy : y ∈ d.Y ⊔ d.S)
    (hxC : x ∈ centralizer (r.cover.borel.W₂ : Set G))
    (hyC : y ∈ centralizer (r.cover.borel.W₁ : Set G)) :
    x*y*x⁻¹*y⁻¹ ∈ d.Y.pCoreIn 2 := by
  have hN (i : OrthogonalPlaneIndex) :
      d.Y ⊔ d.S ≤ normalizer (d.action.plane i : Set G) :=
    sup_le (RankTwo.perfect_normalizes_planes d.action
      (Chapter14.SourcePreliminaries.sourceResidual_le _ _) (residualY_isPPerfect _ _) i)
      (RankTwo.planeStabilizer_normalizes_planes d.action d.T d.sylow_le 1 i)
  have hN₁ : d.Y ⊔ d.S ≤ normalizer (r.cover.borel.W₁ : Set G) := by
    rcases r.cover.borel.planes with ⟨h₁,_⟩ | ⟨h₁,_⟩ <;> rw [h₁] <;> exact hN _
  have hN₂ : d.Y ⊔ d.S ≤ normalizer (r.cover.borel.W₂ : Set G) := by
    rcases r.cover.borel.planes with ⟨_,h₂⟩ | ⟨_,h₂⟩ <;> rw [h₂] <;> exact hN _
  have hC₁ : x*y*x⁻¹*y⁻¹ ∈ centralizer (r.cover.borel.W₁ : Set G) :=
    (centralizer _).mul_mem
      ((mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer _ (hN₁ hx)) y).mp hyC)
      ((centralizer _).inv_mem hyC)
  have hC₂ : x*y*x⁻¹*y⁻¹ ∈ centralizer (r.cover.borel.W₂ : Set G) := by
    have hh := (centralizer (r.cover.borel.W₂ : Set G)).mul_mem hxC
      ((mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer _ (hN₂ hy)) x⁻¹).mp
        ((centralizer _).inv_mem hxC))
    simpa only [mul_assoc] using hh
  have hV : r.cover.borel.W₁ ⊔ r.cover.borel.W₂ = d.V := by
    rcases r.cover.borel.planes with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> rw [h₁,h₂] <;>
      exact RankTwo.natural_planes_sup d.action (by decide)
  apply (natural_kernel_YS s h r).le
  refine ⟨(d.Y ⊔ d.S).mul_mem ((d.Y ⊔ d.S).mul_mem
    ((d.Y ⊔ d.S).mul_mem hx hy) ((d.Y ⊔ d.S).inv_mem hx))
    ((d.Y ⊔ d.S).inv_mem hy), ?_⟩
  rw [← hV]
  have hc : r.cover.borel.W₁ ⊔ r.cover.borel.W₂ ≤ centralizer {x*y*x⁻¹*y⁻¹} :=
    sup_le (fun z hz => mem_centralizer_singleton_iff.mpr (hC₁ z hz))
      (fun z hz => mem_centralizer_singleton_iff.mpr (hC₂ z hz))
  exact fun z hz => mem_centralizer_singleton_iff.mp (hc hz)

/-- The graph reflection fixes the literal component factor modulo the two-core. -/
theorem source_first_fixes_component_modulo {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L)
    (a : NaturalOrthogonalAction d.M d.V) (hYSM : d.Y ⊔ d.S ≤ d.M)
    (hplane : a.plane 1 = r.cover.borel.W₁)
    (c : NaturalCoordinates d.T d.M d.Y d.S (d.Y.pCoreIn 2) d.V r.cover.borel.W₁
      a d.sylow_le hYSM)
    (t : d.T) (ht : c.tProjection t = .sr 0) :
    ∀ x ∈ componentPart d.Yplus L, (t : G)*x*(t : G)⁻¹*x⁻¹ ∈ d.Y.pCoreIn 2 := by
  intro x hx
  apply source_cross_plane_commutator s h r
  · apply mem_sup_right
    apply (c.s_preimage t).mpr
    rw [ht]
    exact Or.inr (Or.inl rfl)
  · exact mem_sup_left (r.cover.plus ▸ ((map_subtype_le _).trans inf_le_left) hx)
  · exact source_first_fixes_second r a hYSM hplane c t ht
  · exact r.cover.borel.component_centralizes hx

/-- The graph reflection inverts the literal opposite factor modulo the two-core. -/
theorem source_first_inverts_opposite_modulo {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L)
    (a : NaturalOrthogonalAction d.M d.V) (hYSM : d.Y ⊔ d.S ≤ d.M)
    (c : NaturalCoordinates d.T d.M d.Y d.S (d.Y.pCoreIn 2) d.V r.cover.borel.W₁
      a d.sylow_le hYSM)
    (t : d.T) (ht : c.tProjection t = .sr 0) :
    ∀ x ∈ planeResidual d.M d.Y r.cover.borel.W₂,
      (t : G)*x*(t : G)⁻¹*x ∈ d.Y.pCoreIn 2 := by
  obtain ⟨f,hf⟩ := c.tOnto (.r 2)
  have htS : (t : G) ∈ d.S := (c.s_preimage t).mpr (by
    rw [ht]
    exact Or.inr (Or.inl rfl))
  have hfS : (f : G) ∈ d.S := (c.s_preimage f).mpr (by
    rw [hf]
    exact Or.inr (Or.inr (Or.inl rfl)))
  let ts : (d.Y ⊔ d.S : Subgroup G) := ⟨t,mem_sup_right htS⟩
  let fs : (d.Y ⊔ d.S : Subgroup G) := ⟨f,mem_sup_right hfS⟩
  let q := c.ysProjection
  have hker (v : (d.Y ⊔ d.S : Subgroup G)) :
      q v = 1 ↔ (v : G) ∈ d.Y.pCoreIn 2 := by
    change v ∈ c.ysProjection.ker ↔ _
    rw [c.ysKernel]
    rfl
  have htf : c.tProjection (t*f) = .sr 2 := by
    rw [map_mul,ht,hf]
    rfl
  intro x hx
  have hxY : x ∈ d.Y := ((planeResidual_le _ _ _).trans inf_le_left) hx
  let xs : (d.Y ⊔ d.S : Subgroup G) := ⟨x,mem_sup_left hxY⟩
  have hcross := source_cross_plane_commutator s h r
    (mem_sup_left hxY) (mem_sup_right (d.S.mul_mem htS hfS))
    ((planeResidual_le _ _ _ hx).2.2) (c.fixes_plane (t*f) htf)
  have hcomm : Commute (q xs) (q ts*q fs) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hh := (hker (xs*(ts*fs)*xs⁻¹*(ts*fs)⁻¹)).mpr hcross
    simpa only [map_mul,map_inv,commutatorElement_def] using hh
  have hfinv : q fs*q xs*(q fs)⁻¹ = (q xs)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have hh := (hker (fs*xs*fs⁻¹*xs)).mpr (c.inverts_modulo f hf x hxY)
    simpa only [map_mul,map_inv] using hh
  have htinv : q ts*q xs*(q ts)⁻¹ = (q xs)⁻¹ := by
    have he : (q ts*q fs)*q xs*(q ts*q fs)⁻¹ = q xs := by
      rw [← hcomm.eq, mul_inv_cancel_right]
    have he' : q ts*(q xs)⁻¹*(q ts)⁻¹ = q xs := by
      calc
        _ = q ts*(q fs*q xs*(q fs)⁻¹)*(q ts)⁻¹ := by rw [hfinv]
        _ = _ := by simpa only [mul_inv_rev, mul_assoc] using he
    have hi := congrArg Inv.inv he'
    simpa only [mul_inv_rev,inv_inv,mul_assoc] using hi
  apply (hker (ts*xs*ts⁻¹*xs)).mp
  simp only [map_mul,map_inv,htinv,inv_mul_cancel]

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.SylowNormalizer
