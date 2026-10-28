module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed.Frames
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.FlagTransport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.HeadPlane
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.CommutatorSpaces

/-!
# Constructing the root frame from the marked generating seed

Fix the source group identification and its natural head. In any basis adapted
to the actual Sylow flag through the seed image plane, a nonzero Sylow-fixed
seed vector has head coordinate e₀. Lift e₁ to the seed: its displacement by
I+E₀₁ has head coordinate e₀ and remains in the seed. Injectivity of the seed
into the proper quotient therefore identifies this displacement with the
original vector in the full module.

The root I+E₀₃ is a nonidentity element of the intrinsic Borel center. The
order-two hypothesis identifies its displacement image with the commutator
space of the specified actor A; conjugacy transfers its dimension to I+E₀₁.
The other fixation assertions follow from membership in the actual Sylow image.
All conjugations use c*g*c⁻¹, consistently with `flagPullback`.

These theorems realize `SeedRootFrame` from the marked seed and the explicit
cyclic conclusions |A| = 2 and dim [U,A] = 2. The natural-or-dual lower-factor
calculation and the final central-root membership remain separate arguments.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed p.962 (PDF p.979).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
open Representation Representation.BinaryOffender ChiefFactors
open CriticalTransfer.MarkedGeometry
open BinaryLinear BinaryLinear.MiddleParabolic

private theorem upper_actor_mem (k : Fin 8) (hk : k = 1 ∨ k = 3 ∨ k = 5) :
    actor k ∈ borel line plane hyperplane := by
  refine ⟨actor_mem k, (mem_plane_parabolic (actor_mem k)).mpr ?_⟩
  rcases hk with rfl | rfl | rfl <;> simp [coordinates, actorFun]

private theorem central_mem_borel : centralRoot ∈ borel line plane hyperplane := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v
    simp [mem_line, centralRoot_apply]
  · intro v
    change centralRoot v 3 = 0 ↔ v 3 = 0
    simp [centralRoot_apply]
  · intro v
    change (centralRoot v 2 = 0 ∧ centralRoot v 3 = 0) ↔ (v 2 = 0 ∧ v 3 = 0)
    simp [centralRoot_apply]

private theorem central_mem_center :
    centralRoot ∈ (Subgroup.center (borel line plane hyperplane)).map
      (borel line plane hyperplane).subtype := by
  refine ⟨⟨centralRoot, central_mem_borel⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro g
  apply Subtype.ext
  ext v i
  change (g : BinaryLinear.GL V) (centralRoot v) i = centralRoot ((g : BinaryLinear.GL V) v) i
  rw [apply_eq_block g.property.1, apply_eq_block g.property.1]
  fin_cases i <;> simp [centralRoot_apply, block]
  ring

private theorem central_ne_one : centralRoot ≠ 1 := by
  intro h
  have hh := congrArg (fun g : BinaryLinear.GL V => g (Pi.single 3 1) 0) h
  simp [centralRoot_apply] at hh

private theorem simple_conjugate_central :
    ∃ t : BinaryLinear.GL V, t * actor 1 * t⁻¹ = centralRoot := by
  let t : BinaryLinear.GL V := LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Equiv.swap (1 : Fin 4) 3)
  refine ⟨t, ?_⟩
  ext v i
  fin_cases i <;> simp [t, LinearEquiv.funCongrLeft_apply, LinearEquiv.funCongrLeft_symm,
    actorFun, centralRoot_apply, Equiv.swap_apply_def]

private theorem fixed_plane_vector (v : V) (hv : v ∈ plane) (hv0 : v ≠ 0)
    (hv1 : actor 1 v = v) : v = Pi.single 0 1 := by
  have hv2 : v 2 = 0 := hv.1
  have hv3 : v 3 = 0 := hv.2
  have hv1' : v 1 = 0 := by
    have hh := congrFun hv1 0
    simpa [actorFun] using hh
  have hv0' : v 0 ≠ 0 := by
    intro h
    apply hv0
    ext i
    fin_cases i <;> simp [h, hv1', hv2, hv3]
  have hone : v 0 = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hv0'
  ext i
  fin_cases i <;> simp [hone, hv1', hv2, hv3]

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

private theorem commSpace_eq_range_of_card_two (ρ : Representation (ZMod 2) H U)
    (A : Subgroup H) (hA : Nat.card A = 2) {z : H} (hzA : z ∈ A) (hz : z ≠ 1) :
    commSpace ρ A = LinearMap.range (ρ z - 1) := by
  obtain ⟨a, _, hall⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  have hz' : (⟨z, hzA⟩ : A) ≠ 1 := fun h => hz (congrArg Subtype.val h)
  have he (b : A) : b = 1 ∨ (b : H) = z := by
    by_cases hb : b = 1
    · exact Or.inl hb
    · exact Or.inr (congrArg Subtype.val ((hall b hb).trans (hall _ hz').symm))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨b, u⟩, rfl⟩
    rcases he b with hb | hb
    · subst b
      simp
    · exact ⟨u, by change ρ z u - u = ρ b u - u; rw [hb]⟩
  · rintro _ ⟨u, rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) ⟨z, hzA⟩ u

private theorem range_conjugate (ρ : Representation (ZMod 2) H U) (t x : H) :
    LinearMap.range (ρ (t * x * t⁻¹) - 1) =
      (LinearMap.range (ρ x - 1)).map (ρ t) := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    refine ⟨ρ x (ρ t⁻¹ u) - ρ t⁻¹ u, ⟨ρ t⁻¹ u, rfl⟩, ?_⟩
    change ρ t (ρ x (ρ t⁻¹ u) - ρ t⁻¹ u) = ρ (t * x * t⁻¹) u - u
    simp [map_sub, ← Module.End.mul_apply, ← map_mul, mul_assoc]
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨ρ t u, ?_⟩
    change ρ (t * x * t⁻¹) (ρ t u) - ρ t u = ρ t (ρ x u - u)
    simp [map_sub, ← Module.End.mul_apply, ← map_mul, mul_assoc]

private theorem simple_rank_eq_central (ρ : Representation (ZMod 2) H U)
    (φ : BinaryLinear.GL V ≃* H) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ (φ (actor 1)) - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ (φ centralRoot) - 1)) := by
  obtain ⟨t, ht⟩ := simple_conjugate_central
  have hc : φ centralRoot = φ t * φ (actor 1) * (φ t)⁻¹ := by
    rw [← ht]
    simp only [map_mul, map_inv]
  rw [hc, range_conjugate]
  exact (LinearEquiv.finrank_map_eq
    (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom (φ t))) _).symm

private theorem borel_map_conj (c : BinaryLinear.GL V)
    (L P F : Submodule (ZMod 2) V)
    (hcL : line.map c.toLinearMap = L) (hcP : plane.map c.toLinearMap = P)
    (hcF : hyperplane.map c.toLinearMap = F) :
    (borel line plane hyperplane).map (MulAut.conj c).toMonoidHom = borel L P F := by
  simp only [borel, middle]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj c).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj c).injective,
    parabolic_map_conj, parabolic_map_conj, parabolic_map_conj, hcL, hcP, hcF]

private theorem center_map_conj_mem (c : BinaryLinear.GL V)
    (L P F : Submodule (ZMod 2) V)
    (hcL : line.map c.toLinearMap = L) (hcP : plane.map c.toLinearMap = P)
    (hcF : hyperplane.map c.toLinearMap = F) :
    MulAut.conj c centralRoot ∈
      (Subgroup.center (borel L P F)).map (borel L P F).subtype := by
  have hb := borel_map_conj c L P F hcL hcP hcF
  obtain ⟨z, hz, hze⟩ := central_mem_center
  have hzc : MulAut.conj c centralRoot ∈ borel L P F := by
    rw [← hb]
    exact Subgroup.mem_map_of_mem _ central_mem_borel
  refine ⟨⟨MulAut.conj c centralRoot, hzc⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro g
  have hg := hb.ge g.property
  obtain ⟨b, hb, he⟩ := hg
  apply Subtype.ext
  have hh := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨b, hb⟩)
  change b * (z : BinaryLinear.GL V) = (z : BinaryLinear.GL V) * b at hh
  change (z : BinaryLinear.GL V) = centralRoot at hze
  rw [hze] at hh
  change (g : BinaryLinear.GL V) * MulAut.conj c centralRoot =
    MulAut.conj c centralRoot * (g : BinaryLinear.GL V)
  change (MulAut.conj c) b = g.val at he
  rw [← he, ← map_mul, ← map_mul, hh]

/-- Every basis adapted to the actual head flag gives the seed root frame.
The displacement ranks are deduced from the order-two central actor and its
commutator dimension; the marked vector is only assumed nonzero and Sylow-fixed. -/
theorem seedRootFrame_of_flag
    (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] NaturalSpace)
    (he : ∀ g u, e (W.quotientRepresentation g u) = eH g (e u))
    (L F : Submodule (ZMod 2) NaturalSpace)
    (hpar : s.parabolic.map eH.toMonoidHom = parabolic (headPlane ρ s W e))
    (hsyl : s.sylow.map eH.toMonoidHom = borel L (headPlane ρ s W e) F)
    (A : Subgroup H)
    (hAc : A = ((Subgroup.center (borel L (headPlane ρ s W e) F)).map
      (borel L (headPlane ρ s W e) F).subtype).comap eH.toMonoidHom)
    (hA : Nat.card A = 2) (hcomm : Module.finrank (ZMod 2) (commSpace ρ A) = 2)
    (v : U) (hv : v ∈ s.space.toSubmodule ⊓ fixedSpace ρ s.sylow) (hv0 : v ≠ 0)
    (c : BinaryLinear.GL NaturalSpace)
    (hcL : line.map c.toLinearMap = L)
    (hcP : plane.map c.toLinearMap = headPlane ρ s W e)
    (hcF : hyperplane.map c.toLinearMap = F) :
    SeedRootFrame ρ (flagPullback eH c) A v := by
  let φ := flagPullback eH c
  have hφ (g : BinaryLinear.GL V) : eH (φ g) = MulAut.conj c g := by
    simp [φ, flagPullback]
  have hb := borel_map_conj c L (headPlane ρ s W e) F hcL hcP hcF
  have hmem (g : BinaryLinear.GL V) (hg : g ∈ borel line plane hyperplane) :
      φ g ∈ s.sylow := by
    have hmap : eH (φ g) ∈ s.sylow.map eH.toMonoidHom := by
      rw [hsyl, hφ, ← hb]
      exact Subgroup.mem_map_of_mem _ hg
    simpa only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] using hmap
  have hfix (g : BinaryLinear.GL V) (hg : g ∈ borel line plane hyperplane) :
      ρ (φ g) v = v := hv.2 ⟨φ g, hmem g hg⟩
  have hzA : φ centralRoot ∈ A := by
    rw [hAc]
    change eH (φ centralRoot) ∈ (Subgroup.center (borel L (headPlane ρ s W e) F)).map
      (borel L (headPlane ρ s W e) F).subtype
    rw [hφ]
    exact center_map_conj_mem c L (headPlane ρ s W e) F hcL hcP hcF
  have hz1 : φ centralRoot ≠ 1 := by
    intro h
    exact central_ne_one (φ.injective (by simpa using h))
  have hzr : Module.finrank (ZMod 2) (LinearMap.range (ρ (φ centralRoot) - 1)) = 2 := by
    rw [← commSpace_eq_range_of_card_two ρ A hA hzA hz1]
    exact hcomm
  refine ⟨hzA, (simple_rank_eq_central ρ φ).trans hzr, hzr, ?_,
    hfix _ (upper_actor_mem 3 (by simp)), hfix _ (upper_actor_mem 5 (by simp)),
    hfix _ central_mem_borel⟩
  let q : U →ₗ[ZMod 2] V :=
    c.symm.toLinearMap.comp (e.toLinearMap.comp W.toSubmodule.mkQ)
  have hq (g : BinaryLinear.GL V) (u : U) : q (ρ (φ g) u) = g (q u) := by
    have hh := he (φ g) (W.toSubmodule.mkQ u)
    change e (W.toSubmodule.mkQ (ρ (φ g) u)) = eH (φ g) (e (W.toSubmodule.mkQ u)) at hh
    simp only [q, LinearMap.comp_apply, LinearEquiv.coe_coe, hh, hφ,
      MulAut.conj_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply]
  have hqi : Function.Injective (q.comp s.space.toSubmodule.subtype) :=
    c.symm.injective.comp (e.injective.comp (s.quotient_injective ρ W hW))
  have hqvP : q v ∈ plane := by
    have hh : e (W.toSubmodule.mkQ v) ∈ headPlane ρ s W e := ⟨⟨v, hv.1⟩, rfl⟩
    rw [← hcP, Submodule.mem_map_equiv] at hh
    exact hh
  have hqv0 : q v ≠ 0 := by
    intro hh
    have hvz := hqi (a₁ := ⟨v, hv.1⟩) (a₂ := 0) (by simpa using hh)
    exact hv0 (congrArg Subtype.val hvz)
  have hqv : q v = Pi.single 0 1 := fixed_plane_vector (q v) hqvP hqv0 (by
    rw [← hq, hfix _ (upper_actor_mem 1 (by simp))])
  have huP : c (Pi.single 1 1) ∈ headPlane ρ s W e := by
    rw [← hcP]
    exact ⟨Pi.single 1 1, by constructor <;> simp, rfl⟩
  obtain ⟨u, hu⟩ := huP
  have hqu : q (u : U) = Pi.single 1 1 := by
    change c.symm (headSeedMap ρ s W e u) = Pi.single 1 1
    rw [hu, c.symm_apply_apply]
  have hxP : φ (actor 1) ∈ s.parabolic := by
    have hh : eH (φ (actor 1)) ∈ s.parabolic.map eH.toMonoidHom := by
      rw [hpar, hφ, ← hcP, ← parabolic_map_conj]
      exact Subgroup.mem_map_of_mem _ (upper_actor_mem 1 (by simp)).2
    simpa only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] using hh
  have hdu : ρ (φ (actor 1)) u - u ∈ s.space.toSubmodule :=
    s.space.toSubmodule.sub_mem
      (s.space.apply_mem_toSubmodule ⟨φ (actor 1), hxP⟩ u.property) u.property
  have hdq : q (ρ (φ (actor 1)) u - u) = q v := by
    rw [map_sub, hq, hqu, hqv]
    ext i
    fin_cases i <;> simp [actorFun]
  have hd : ρ (φ (actor 1)) u - u = v :=
    congrArg Subtype.val (hqi (a₁ := ⟨_, hdu⟩) (a₂ := ⟨v, hv.1⟩) hdq)
  exact ⟨u, hd⟩

/-- Adapt the coordinates to the marked seed plane and actual Sylow flag, and
construct all fields of `SeedRootFrame` from the seed and cyclic rank data. -/
theorem exists_seedRootFrame
    (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] NaturalSpace)
    (he : ∀ g u, e (W.quotientRepresentation g u) = eH g (e u))
    (L F : Submodule (ZMod 2) NaturalSpace)
    (hLP : L ≤ headPlane ρ s W e) (hPF : headPlane ρ s W e ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1) (hF : Module.finrank (ZMod 2) F = 3)
    (hpar : s.parabolic.map eH.toMonoidHom = parabolic (headPlane ρ s W e))
    (hsyl : s.sylow.map eH.toMonoidHom = borel L (headPlane ρ s W e) F)
    (A : Subgroup H)
    (hAc : A = ((Subgroup.center (borel L (headPlane ρ s W e) F)).map
      (borel L (headPlane ρ s W e) F).subtype).comap eH.toMonoidHom)
    (hA : Nat.card A = 2) (hcomm : Module.finrank (ZMod 2) (commSpace ρ A) = 2)
    (v : U) (hv : v ∈ s.space.toSubmodule ⊓ fixedSpace ρ s.sylow) (hv0 : v ≠ 0) :
    ∃ c : BinaryLinear.GL NaturalSpace,
      line.map c.toLinearMap = L ∧
      plane.map c.toLinearMap = headPlane ρ s W e ∧
      hyperplane.map c.toLinearMap = F ∧
      SeedRootFrame ρ (flagPullback eH c) A v := by
  obtain ⟨c, hcL, hcP, hcF⟩ := exists_flag_equiv L (headPlane ρ s W e) F
    hLP hPF hL (headPlane_finrank ρ s W hW e) hF
  exact ⟨c, hcL, hcP, hcF, seedRootFrame_of_flag ρ s W hW eH e he L F
    hpar hsyl A hAc hA hcomm v hv hv0 c hcL hcP hcF⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
