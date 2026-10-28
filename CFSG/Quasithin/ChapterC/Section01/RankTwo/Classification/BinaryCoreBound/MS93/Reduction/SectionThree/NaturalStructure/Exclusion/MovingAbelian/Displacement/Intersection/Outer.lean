module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Displacement.Intersection

/-!
# The full outer-extension radius intersection

For the critical endpoints a, a', put D = [X_a,X_a']. A critical involution
has displacement W of dimension at least two inside D, and D lies in U_a'.
The full fixed part C is disjoint from U_a'. Since the marked action on X
has fixed codimension four, C + W has codimension at most two.

An element of V_a intersect Q_c has two-power order, lies in the endpoint
stabilizer, and centralizes D because V_a lies in Q_a. It therefore fixes
C + W. The linear calculation below puts its entire X-displacement in
C + W. The displacement also lies in U_a', so disjointness removes the
C component and puts it in W, hence in D. In particular X and Z remain
distinct in the index-two outer extension.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.2)(v), printed p.863, and the radius-intersection paragraph of
(3.8), printed p.878. The private linear argument extends the nilpotent
fixed-plane calculation in SourceCalculation.Central.FixedPlane to retain
the full fixed part.
-/

public section

open Representation Representation.BinaryOffender
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open ModuleAlternatives SourceCalculation

section Linear

variable {G T : Type*} [Group G] [AddCommGroup T] [Module (ZMod 2) T]
  [FiniteDimensional (ZMod 2) T]

private theorem codim_pow_le (ρ : Representation (ZMod 2) G T) (g : G) (n : ℕ) :
    fixedCodim ρ (Subgroup.zpowers (g ^ n)) ≤ fixedCodim ρ (Subgroup.zpowers g) := by
  have h := Submodule.finrank_mono (fixedSpace_antitone ρ
    (Subgroup.zpowers_le.mpr ((Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers g) n)))
  have h₁ := fixedCodim_add_finrank ρ (Subgroup.zpowers (g ^ n))
  have h₂ := fixedCodim_add_finrank ρ (Subgroup.zpowers g)
  omega

private theorem two_le_codim (ρ : Representation (ZMod 2) G T)
    (hm : ∀ g : G, g ^ 2 = 1 → g ≠ 1 → 2 ≤ fixedCodim ρ (Subgroup.zpowers g))
    (n : ℕ) (g : G) (hp : g ^ (2 ^ n) = 1) (hne : g ≠ 1) :
    2 ≤ fixedCodim ρ (Subgroup.zpowers g) := by
  induction n generalizing g with
  | zero => simp only [pow_zero, pow_one] at hp; exact (hne hp).elim
  | succ n ih =>
    by_cases h : g ^ 2 = 1
    · exact hm g h hne
    · have hp' : (g ^ 2) ^ (2 ^ n) = 1 := by
        rw [← pow_mul, ← pow_succ']; exact hp
      exact (ih (g ^ 2) hp' h).trans (codim_pow_le ρ g 2)

/-- A two-element fixing a subspace of codimension at most two has its
displacement in that subspace when involutions move at least two dimensions. -/
private theorem displacement_le_fixed_codim_two (ρ : Representation (ZMod 2) G T)
    (hm : ∀ g : G, g ^ 2 = 1 → g ≠ 1 → 2 ≤ fixedCodim ρ (Subgroup.zpowers g))
    (W : Submodule (ZMod 2) T)
    (hdim : Module.finrank (ZMod 2) T ≤ Module.finrank (ZMod 2) W + 2)
    (g : G) (hp : ∃ n : ℕ, g ^ (2 ^ n) = 1)
    (hfix : W ≤ fixedSpace ρ (Subgroup.zpowers g)) :
    LinearMap.range (ρ g - LinearMap.id) ≤ W := by
  by_cases hg : g = 1
  · subst g
    simp [Module.End.one_eq_id]
  obtain ⟨n, hn⟩ := hp
  have hlow := two_le_codim ρ hm n g hn hg
  have hcod := fixedCodim_add_finrank ρ (Subgroup.zpowers g)
  let : Nontrivial T := Module.nontrivial_of_finrank_pos (R := ZMod 2) (M := T) (by omega)
  let : CharP (Module.End (ZMod 2) T) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (Module.End (ZMod 2) T)).injective 2
  let N : Module.End (ZMod 2) T := ρ g - 1
  have hker : N.ker = fixedSpace ρ (Subgroup.zpowers g) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    exact sub_eq_zero
  have hmono := Submodule.finrank_mono hfix
  have hcodim : fixedCodim ρ (Subgroup.zpowers g) = 2 := by omega
  have hrank : Module.finrank (ZMod 2) N.range = 2 := by
    simpa only [fixedCodim_zpowers_eq_displacement_rank, N, Module.End.one_eq_id] using hcodim
  have hnil : N ^ (2 ^ n) = 0 := by
    dsimp only [N]
    rw [sub_pow_char_pow_of_commute 2 n (Commute.one_right _),
      ← map_pow, hn, map_one, one_pow, sub_self]
  have hN2 : N ^ 2 = ρ (g ^ 2) - 1 := by
    dsimp only [N]
    rw [sub_pow_char_of_commute 2 (Commute.one_right _), ← map_pow, one_pow]
  -- A nontrivial square would stabilize the first two kernels of a nilpotent map.
  have hg2 : g ^ 2 = 1 := by
    by_contra hg2
    have hp2 : (g ^ 2) ^ (2 ^ n) = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hn, one_pow]
    have hlow2 := two_le_codim ρ hm n (g ^ 2) hp2 hg2
    rw [fixedCodim_zpowers_eq_displacement_rank] at hlow2
    have hkerle : N.ker ≤ (N ^ 2).ker := by
      simpa only [pow_two, Module.End.mul_eq_comp] using LinearMap.ker_le_ker_comp N N
    have hk1 := N.finrank_range_add_finrank_ker
    have hk2 := (N ^ 2).finrank_range_add_finrank_ker
    have hkmono := Submodule.finrank_mono hkerle
    have heq : N.ker = (N ^ 2).ker := by
      apply Submodule.eq_of_le_of_finrank_eq hkerle
      change 2 ≤ Module.finrank (ZMod 2) (ρ (g ^ 2) - 1).range at hlow2
      rw [← hN2] at hlow2
      omega
    have he := Module.End.ker_pow_constant (f := N) (k := 1) (by simpa using heq)
      (2 ^ n - 1)
    have hpos : 0 < 2 ^ n := by positivity
    rw [show 1 + (2 ^ n - 1) = 2 ^ n by omega, hnil, LinearMap.ker_zero,
      pow_one] at he
    have hz := LinearMap.ker_eq_top.mp he
    rw [hz, LinearMap.range_zero, finrank_bot] at hrank
    omega
  have hsq : N ^ 2 = 0 := by rw [hN2, hg2, map_one, sub_self]
  have heq : W = N.ker := by
    rw [hker]
    exact Submodule.eq_of_le_of_finrank_eq hfix (by omega)
  rw [heq]
  rintro v ⟨w, rfl⟩
  change N (N w) = 0
  have hh := LinearMap.congr_fun hsq w
  exact hh

end Linear
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The full critical-endpoint intersection bound in the index-two outer
extension, retaining the actual X actor. -/
theorem outerExtension_radius_intersection_X (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (h : OuterExtension source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (c : Vertex R) (_hac : (cosetGraph R).dist a c = 2)
    (hca' : (cosetGraph R).dist c a' = 2) :
    ⁅V R a ⊓ Q R c, X R a'⁆ ≤ ⁅X R a, X R a'⁆ := by
  classical
  let := X_elementary R (alpha R)
  let := X_elementary R a
  let := finite_X R (alpha R)
  let ρ := Offenders.linearize (xAction source)
  have hb0 : 0 < geometry.b R := by omega
  have ha' := critical_endpoint_color R a ha _ hc
  obtain ⟨frame⟩ := exists_frame a' ha'
  have hdis := (outerExtension_at source h a' frame).2.2.1
  let D := ⁅X R a, X R a'⁆
  have hDU : D ≤ U R a' := Outer.critical_commutator_le_U source geometry hb0 h a ha a' hc
  have hDX : D ≤ X R a :=
    (critical_commutator_le_intersection source geometry hb0 a ha a' hc).trans inf_le_left
  have hm : ∀ g : SL, g ^ 2 = 1 → g ≠ 1 → 2 ≤ fixedCodim ρ (zpowers g) :=
    Models.outerExtension_involutionBound source geometry hb0 h
  have hact (g : stabilizer R a') (x : X R (alpha R)) :
      frame.conjugation (xAction source (frame.projection source g) x : FreeAmalgam R) =
        (g : FreeAmalgam R) * frame.conjugation (x : FreeAmalgam R) *
          (g : FreeAmalgam R)⁻¹ := by
    obtain ⟨m, rfl⟩ := frame.localEquiv.surjective g
    rw [frame.projection_localEquiv, xAction, layerAction_apply, map_mul, map_mul,
      map_inv, ← frame.localEquiv_val]
  have hZX : Z R a ≤ X R a := geometry.omega_bound a ha (by
    rw [geometry.distance_constant a ha]; exact hb0)
  obtain ⟨z, hz, hzQ⟩ := Set.not_subset.mp hc.2
  have hzX := hZX hz
  have hzS := critical_X_le_stabilizer source geometry hb0 a ha a' hc hzX
  let g : SL := frame.projection source ⟨z, hzS⟩
  have hg2 : g ^ 2 = 1 := by
    rw [← map_pow]
    have hz2 : (⟨z, hzS⟩ : stabilizer R a') ^ 2 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hzX)
    rw [hz2, map_one]
  have hgne : g ≠ 1 := by
    intro he
    have hh : (⟨z, hzS⟩ : stabilizer R a') ∈ (frame.projection source).ker := he
    rw [frame.projection_kernel] at hh
    exact hzQ hh
  let W := LinearMap.range (ρ g - LinearMap.id)
  have hW : 2 ≤ Module.finrank (ZMod 2) W := by
    simpa only [fixedCodim_zpowers_eq_displacement_rank] using hm g hg2 hgne
  have hWD (w : W) : frame.conjugation (w.val.toMul : FreeAmalgam R) ∈ D := by
    obtain ⟨v, hv⟩ := w.property
    rw [← hv]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, toMul_sub, div_eq_mul_inv,
      Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    change frame.conjugation (xAction source g v.toMul : FreeAmalgam R) *
      (frame.conjugation (v.toMul : FreeAmalgam R))⁻¹ ∈ D
    rw [hact]
    exact commutator_mem_commutator hzX (by
      rw [← frame.map_X]
      exact mem_map_of_mem _ v.toMul.property)
  -- Include every fixed vector before applying the codimension-two calculation.
  let F := fixedSpace ρ ⊤
  have hFC (v : Additive (X R (alpha R))) (hv : v ∈ F) :
      frame.conjugation (v.toMul : FreeAmalgam R) ∈ fixedAt R a' := by
    rw [frame.mem_fixedAt]
    refine ⟨v.toMul.property, ?_⟩
    apply (layerAction_fixed_iff source (X R (alpha R)) (X_normalized R (alpha R))
      (Q_le_centralizer_X R (alpha R)) v.toMul).mp
    intro g
    exact congrArg Additive.toMul (hv ⟨g, mem_top g⟩)
  have hFW : Disjoint F W := by
    apply Submodule.disjoint_def.mpr
    intro v hvF hvW
    have he : frame.conjugation (v.toMul : FreeAmalgam R) = 1 :=
      (Subgroup.disjoint_def.mp hdis) (hFC v hvF) (hDU (hWD ⟨v, hvW⟩))
    apply Additive.toMul.injective
    apply Subtype.ext
    apply frame.conjugation.injective
    change frame.conjugation (v.toMul : FreeAmalgam R) = frame.conjugation 1
    simpa only [map_one] using he
  have hdim : Module.finrank (ZMod 2) (Additive (X R (alpha R))) ≤
      Module.finrank (ZMod 2) (F ⊔ W : Submodule (ZMod 2) (Additive (X R (alpha R)))) + 2 := by
    have hcod := fixedCodim_add_finrank ρ ⊤
    have hfour := Models.outerExtension_fixedCodim_top source geometry hb0 h
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq F W
    rw [hFW.eq_bot, finrank_bot, add_zero] at hsum
    change fixedCodim ρ ⊤ = 4 at hfour
    change fixedCodim ρ ⊤ + Module.finrank (ZMod 2) F = _ at hcod
    omega
  let Y := V R a ⊓ Q R c
  have hYQ : Y ≤ Q R a := inf_le_left.trans (geometry.V_le_Q hb a ha)
  have hYC : Y ≤ centralizer (D : Set (FreeAmalgam R)) :=
    (hYQ.trans (Q_le_centralizer_X R a)).trans (centralizer_le hDX)
  obtain ⟨t, hct, ha't⟩ := exists_common_neighbor_of_dist_two R c a' hca'
  have ht : color R t = true := by
    have hn := adjacent_color_ne R ha't
    cases he : color R t <;> simp_all
  have hYS : Y ≤ stabilizer R a' := fun y hy =>
    (Q_le_adjacent_h R ht hct hy.2).2 a' (adjacent_symm R ha't)
  apply commutator_le.mpr
  intro y hy x hx
  let yS : stabilizer R a' := ⟨y, hYS hy⟩
  let ybar := frame.projection source yS
  have hp : ∃ n : ℕ, ybar ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := (kernel_isPGroup source c).exists_pow_pow_eq_one ⟨y, hy.2⟩
    have hh : yS ^ (2 ^ n) = 1 :=
      Subtype.ext (congrArg (fun q : Q R c => (q : FreeAmalgam R)) hn)
    exact ⟨n, by rw [← map_pow, hh, map_one]⟩
  have hfix : F ⊔ W ≤ fixedSpace ρ (zpowers ybar) := by
    apply sup_le (fixedSpace_antitone ρ le_top)
    intro w hw
    rw [mem_fixedSpace_zpowers_iff]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply frame.conjugation.injective
    change frame.conjugation (xAction source ybar w.toMul : FreeAmalgam R) =
      frame.conjugation (w.toMul : FreeAmalgam R)
    rw [hact]
    have hh := hYC hy _ (hWD ⟨w, hw⟩)
    change frame.conjugation (w.toMul : FreeAmalgam R) * y =
      y * frame.conjugation (w.toMul : FreeAmalgam R) at hh
    change y * frame.conjugation (w.toMul : FreeAmalgam R) * y⁻¹ = _
    rw [← hh, mul_inv_cancel_right]
  let eX : X R (alpha R) ≃* X R a' :=
    (frame.conjugation.subgroupMap (X R (alpha R))).trans (MulEquiv.subgroupCongr frame.map_X)
  let v := Additive.ofMul (eX.symm ⟨x, hx⟩)
  have hv : frame.conjugation (v.toMul : FreeAmalgam R) = x :=
    congrArg Subtype.val (eX.apply_symm_apply ⟨x, hx⟩)
  have hmem : ρ ybar v - v ∈ F ⊔ W :=
    displacement_le_fixed_codim_two ρ hm (F ⊔ W) hdim ybar hp hfix ⟨v, rfl⟩
  obtain ⟨f, hf, w, hw, he⟩ := Submodule.mem_sup.mp hmem
  have hmul : frame.conjugation (f.toMul : FreeAmalgam R) *
      frame.conjugation (w.toMul : FreeAmalgam R) = ⁅y, x⁆ := by
    have hh := congrArg (fun v : Additive (X R (alpha R)) =>
      frame.conjugation (v.toMul : FreeAmalgam R)) he
    simp only [toMul_add, toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      map_mul, map_inv] at hh
    change _ = frame.conjugation (xAction source ybar v.toMul : FreeAmalgam R) *
      (frame.conjugation (v.toMul : FreeAmalgam R))⁻¹ at hh
    rw [hact, hv] at hh
    exact hh
  -- The independent U-containment eliminates the fixed component.
  have hcommU : ⁅y, x⁆ ∈ U R a' := by
    have hh : ⁅stabilizer R a', X R a'⁆ ≤ U R a' := by
      rw [commutator_comm]
      exact Outer.X_commutator_le_U source geometry hb0 h a' ha'
    exact hh (commutator_mem_commutator (hYS hy) hx)
  have hfU : frame.conjugation (f.toMul : FreeAmalgam R) ∈ U R a' := by
    have hh := (U R a').mul_mem hcommU ((U R a').inv_mem (hDU (hWD ⟨w, hw⟩)))
    rwa [← hmul, mul_inv_cancel_right] at hh
  have hf1 : frame.conjugation (f.toMul : FreeAmalgam R) = 1 :=
    (Subgroup.disjoint_def.mp hdis) (hFC f hf) hfU
  rw [hf1, one_mul] at hmul
  exact hmul ▸ hWD ⟨w, hw⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
