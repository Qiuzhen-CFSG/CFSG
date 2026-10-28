module
public import Theory.Representation.G2BinaryPointSmallImage
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The three-space inside a second point-parabolic kernel

For the binary natural G₂ point parabolic, root A and C displacements of
the invariant hyperplane span the marked three-space. In an extension by
the natural E₆₄ module, a normal two-subgroup of order 1024 intersecting
that module in order 32 maps onto the whole point-parabolic two-core.
Consequently every invariant order-eight subgroup of the original module
lies in the commutator subgroup of that second kernel.

The proof compares the two actual kernels and identifies their intersection
as the natural hyperplane by invariance. No full ambient Sylow placement,
Frattini identification, or assertion about all involutions is required.
The consumer is Chapter13's OriginalOddNormalizer.RudvalisThreeSpace.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612. The inherited root
coordinates retain their ATLAS attribution in LICENSES/ATLAS.txt.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Subgroup
open scoped IsMulCommutative
local notation "ρ" => Restricted.NaturalCoordinates.action F

/-- The point core moves the hyperplane through the whole marked three-space. -/
theorem seed_le_of_core_hyperplane_displacements (S : Submodule F W)
    (hS : ∀ a ∈ BinaryCore.secondParabolic.pCoreIn 2,
      ∀ v ∈ hyperplane, ρ a v - v ∈ S) : seed ≤ S := by
  have hroot (i : Fin 6) (hi : i ≠ 4) :
      unipotentProduct (Pi.single i (1:F)) ∈ BinaryCore.secondParabolic.pCoreIn 2 := by
    rw [←LieParabolicSetup.local₂_binary,LieParabolicSetup.local₂_pCoreIn]
    exact ⟨Pi.single i 1,by simp [Ne.symm hi],rfl⟩
  have hA : rootA (1:F) ∈ BinaryCore.secondParabolic.pCoreIn 2 := by
    simpa [unipotentProduct] using hroot 0 (by decide)
  have hC : rootC (1:F) ∈ BinaryCore.secondParabolic.pCoreIn 2 := by
    simpa [unipotentProduct] using hroot 2 (by decide)
  have h0 : (Pi.single 0 1 : W) ∈ S := by
    convert hS _ hA (Pi.single 4 1) (by simp) using 1
    ext i
    fin_cases i <;> simp
  have h1 : (Pi.single 1 1 : W) ∈ S := by
    convert hS _ hC (Pi.single 3 1) (by simp) using 1
    ext i
    fin_cases i <;> simp
  have h2 : (Pi.single 2 1 : W) ∈ S := by
    convert hS _ hC (Pi.single 4 1) (by simp) using 1
    ext i
    fin_cases i <;> simp
  intro v hv
  obtain ⟨h3,h4,h5⟩ := (mem_seed v).mp hv
  have he : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp [h3,h4,h5]
  rw [he]
  exact S.add_mem (S.add_mem (S.smul_mem _ h0) (S.smul_mem _ h1)) (S.smul_mem _ h2)

private theorem subspace_eq_of_card {S R : Submodule F W} (h : S ≤ R)
    (hc : Nat.card R ≤ Nat.card S) : S = R := by
  have hs := ((Submodule.inclusion_injective h).bijective_of_nat_card_le hc).surjective
  apply le_antisymm h
  intro x hx
  obtain ⟨v,hv⟩ := hs ⟨x,hx⟩
  have he : v.val = x := congrArg Subtype.val hv
  exact he ▸ v.property

/-- Invariance and order identify both steps of the point flag. -/
theorem point_invariant_subspace_of_card (S : Submodule F W)
    (hS : ∀ a ∈ BinaryCore.secondParabolic, ∀ v ∈ S, ρ a v ∈ S) :
    (Nat.card S = 8 → S = seed) ∧ (Nat.card S = 32 → S = hyperplane) := by
  constructor
  · intro hc
    by_cases hs : S ≤ seed
    · exact subspace_eq_of_card hs (by rw [hc,card_seed])
    · exact (subspace_eq_of_card
        (seed_le_of_point_invariant_not_le_seed S hS hs) (by rw [hc,card_seed])).symm
  · intro hc
    rcases large_point_invariant_subspace S hS (by omega) with h | h
    · exact h
    · have ht : Nat.card (⊤ : Submodule F W) = 64 := by simp [F,W]
      rw [h,ht] at hc
      omega

end Atlas.G2.Natural.BinaryPointFlag

namespace Theory.GroupTheory
open Subgroup
/-- Equal kernel-image orders identify the image with the whole two-core. -/
theorem map_eq_pCore_of_kernel_intersection
    {P B : Type*} [Group P] [Finite P] [Group B] [Finite B]
    (b : P →* B) (hb : Function.Surjective b) (R : Subgroup P) [R.Normal]
    (hR : IsPGroup 2 R) (hcard : Nat.card R = 1024)
    (hinter : Nat.card (R ⊓ b.ker : Subgroup P) = 32)
    (hcore : Nat.card (pCore 2 B) = 32) : R.map b = pCore 2 B := by
  let : (R.map b).Normal := Subgroup.Normal.map inferInstance b hb
  have hle : R.map b ≤ pCore 2 B := le_sSup ⟨inferInstance,hR.map b⟩
  have hm := IsElementaryAbelian.card_inf_ker_mul_card_map R b
  rw [hinter,hcard] at hm
  apply eq_of_le_of_card_ge hle
  rw [hcore]
  omega
end Theory.GroupTheory

namespace Atlas.G2.Natural.BinaryPointFlag
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
local notation "ρ" => Restricted.NaturalCoordinates.action F
variable {P : Type*} [Group P] [Finite P]

private def coordinatesSubgroup {E : Subgroup P} [IsElementaryAbelian 2 E]
    (e : Additive E ≃ₗ[F] W) (A : Subgroup P) : Submodule F W :=
  (AddSubgroup.toZModSubmodule 2 (A.subgroupOf E).toAddSubgroup).map e.toLinearMap

omit [Finite P] in
private theorem mem_coordinatesSubgroup {E : Subgroup P} [IsElementaryAbelian 2 E]
    (e : Additive E ≃ₗ[F] W) (A : Subgroup P) (v : Additive E) :
    e v ∈ coordinatesSubgroup e A ↔ (v.toMul : P) ∈ A := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact e.injective he ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

omit [Finite P] in
private theorem card_coordinatesSubgroup {E : Subgroup P} [IsElementaryAbelian 2 E]
    (e : Additive E ≃ₗ[F] W) (A : Subgroup P) (hA : A ≤ E) :
    Nat.card (coordinatesSubgroup e A) = Nat.card A := by
  let d : A ≃ coordinatesSubgroup e A := {
    toFun := fun v => ⟨e (Additive.ofMul ⟨v.val,hA v.property⟩),
      (mem_coordinatesSubgroup e A _).mpr v.property⟩
    invFun := fun v => ⟨(e.symm v.val).toMul,
      (mem_coordinatesSubgroup e A (e.symm v.val)).mp (by rw [e.apply_symm_apply]; exact v.property)⟩
    left_inv := fun v => by simp only [e.symm_apply_apply]; rfl
    right_inv := fun v => Subtype.ext (e.apply_symm_apply v.val) }
  exact (Nat.card_congr d).symm

/-- In a natural point-parabolic extension, the original invariant three-space
lies in the derived subgroup of a second normal two-kernel of order 1024.
The two kernels remain distinct; their intersection has order 32. -/
theorem invariant_three_le_second_kernel_commutator
    (b : P →* BinaryCore.secondParabolic) (hb : Function.Surjective b)
    [IsElementaryAbelian 2 b.ker]
    (e : Additive b.ker ≃ₗ[F] W)
    (he : ∀ (x : P) (v : b.ker),
      e (Additive.ofMul ⟨x * v * x⁻¹,
        (inferInstance : b.ker.Normal).conj_mem v v.property x⟩) =
        ρ (b x) (e (Additive.ofMul v)))
    (R : Subgroup P) [R.Normal] (hR : IsPGroup 2 R)
    (hcard : Nat.card R = 1024)
    (hinter : Nat.card (R ⊓ b.ker : Subgroup P) = 32)
    (U : Subgroup P) [U.Normal] (hU : U ≤ b.ker) (hUcard : Nat.card U = 8) :
    U ≤ ⁅R,R⁆ := by
  have hcore : Nat.card (pCore 2 BinaryCore.secondParabolic) = 32 := by
    rw [←LieParabolicSetup.local₂_binary]
    exact LieParabolicSetup.card_local₂_pCore_binary
  have hmap : R.map b = pCore 2 BinaryCore.secondParabolic :=
    map_eq_pCore_of_kernel_intersection b hb R hR hcard hinter hcore
  have hinvariant (A : Subgroup P) [A.Normal] :
      ∀ a ∈ BinaryCore.secondParabolic, ∀ v ∈ coordinatesSubgroup e A, ρ a v ∈ coordinatesSubgroup e A := by
    intro a ha v hv
    obtain ⟨x,hx⟩ := hb ⟨a,ha⟩
    obtain ⟨v,rfl⟩ := e.surjective v
    have hm := (mem_coordinatesSubgroup e A v).mp hv
    have hax : (b x : Model F) = a := congrArg Subtype.val hx
    have heq := he x v.toMul
    simp only [ofMul_toMul] at heq
    rw [←hax,←heq]
    exact (mem_coordinatesSubgroup e A _).mpr
      ((inferInstance : A.Normal).conj_mem _ hm x)
  have hhyper : coordinatesSubgroup e (R ⊓ b.ker) = hyperplane :=
    (point_invariant_subspace_of_card _ (hinvariant _)).2
      ((card_coordinatesSubgroup e _ inf_le_right).trans hinter)
  have hseed : coordinatesSubgroup e U = seed :=
    (point_invariant_subspace_of_card _ (hinvariant _)).1
      ((card_coordinatesSubgroup e _ hU).trans hUcard)
  have hspan : seed ≤ coordinatesSubgroup e ⁅R,R⁆ := by
    apply seed_le_of_core_hyperplane_displacements
    intro a ha v hv
    obtain ⟨a',ha',haa⟩ := ha
    have haR : a' ∈ R.map b := hmap.symm ▸ ha'
    obtain ⟨x,hx,hxa⟩ := haR
    obtain ⟨v,rfl⟩ := e.surjective v
    have hvR : (v.toMul : P) ∈ R :=
      ((mem_coordinatesSubgroup e (R ⊓ b.ker) v).mp (hhyper.symm ▸ hv)).1
    have hax : (b x : Model F) = a := (congrArg Subtype.val hxa).trans haa
    have heq := he x v.toMul
    simp only [ofMul_toMul] at heq
    rw [←hax,←heq,←map_sub]
    apply (mem_coordinatesSubgroup e ⁅R,R⁆ _).mpr
    simp only [toMul_sub,toMul_ofMul,div_eq_mul_inv]
    change x * v.toMul.val * x⁻¹ * v.toMul.val⁻¹ ∈ ⁅R,R⁆
    exact commutator_mem_commutator hx hvR
  intro u hu
  let v : Additive b.ker := Additive.ofMul ⟨u,hU hu⟩
  exact (mem_coordinatesSubgroup e ⁅R,R⁆ v).mp
    (hspan (hseed ▸ (mem_coordinatesSubgroup e U v).mpr hu))

/-- The same placement through an original multiplicative module marking.
The additive kernel instance is constructed at this small interface. -/
theorem invariant_three_le_second_kernel_commutator_of_marking
    {V : Type*} [Group V] [IsElementaryAbelian 2 V]
    (b : P →* BinaryCore.secondParabolic) (hb : Function.Surjective b)
    (d : b.ker ≃* V) (coords : Additive V ≃ₗ[F] Natural.Space F)
    (a : P →* Model F) (g : Model F)
    (hmark : ∀ x, (b x : Model F) = g * a x * g⁻¹)
    (he : ∀ (x : P) (v : b.ker),
      coords (Additive.ofMul (d ⟨x * v * x⁻¹,
        (inferInstance : b.ker.Normal).conj_mem v v.property x⟩)) =
        Natural.action F (a x) (coords (Additive.ofMul (d v))))
    (R : Subgroup P) [R.Normal] (hR : IsPGroup 2 R)
    (hcard : Nat.card R = 1024)
    (hinter : Nat.card (R ⊓ b.ker : Subgroup P) = 32)
    (U : Subgroup P) [U.Normal] (hU : U ≤ b.ker) (hUcard : Nat.card U = 8) :
    U ≤ ⁅R,R⁆ := by
  let hbelem : IsElementaryAbelian 2 b.ker :=
    IsElementaryAbelian.of_surjective d.symm.toMonoidHom d.symm.surjective
  let : IsMulCommutative b.ker := hbelem.toIsMulCommutative
  let : Module F (Additive b.ker) := IsElementaryAbelian.isVectorSpace 2
  let ed : Additive b.ker ≃ₗ[F] Additive V :=
    { d.toAdditive with map_smul' := ZMod.map_smul d.toAdditive }
  let t := LinearMap.GeneralLinearGroup.toLinearEquiv ((Natural.action F).asGroupHom g)
  let coord := Restricted.NaturalCoordinates.equiv F
  let θ := ((ed.trans coords).trans t).trans coord
  have hθ (x : P) (v : b.ker) :
      θ (Additive.ofMul ⟨x * v * x⁻¹,
        (inferInstance : b.ker.Normal).conj_mem v v.property x⟩) =
      ρ (b x) (θ (Additive.ofMul v)) := by
    change coord (Natural.action F g (coords (Additive.ofMul (d _)))) = _
    simp only [toMul_ofMul]
    rw [he]
    have hh := LinearMap.congr_fun
      ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' (b x))
      (Natural.action F g (coords (Additive.ofMul (d v))))
    change coord (Natural.action F (b x)
      (Natural.action F g (coords (Additive.ofMul (d v))))) =
      ρ (b x) (θ (Additive.ofMul v)) at hh
    rw [←hh]
    congr 1
    rw [hmark]
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  exact invariant_three_le_second_kernel_commutator b hb θ hθ R hR hcard hinter U hU hUcard
end Atlas.G2.Natural.BinaryPointFlag
