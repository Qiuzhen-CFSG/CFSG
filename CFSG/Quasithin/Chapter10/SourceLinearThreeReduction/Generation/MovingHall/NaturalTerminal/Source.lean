module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.TorusAxes
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.FixedCenter
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OriginalFixedCenter
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.BlockAlternative
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.AlphaEntrance
public import Theory.Representation.SL2.PairedOddAxes
public import Theory.GroupTheory.CoprimeCentralizerCard
public import Theory.Representation.BinaryConjugationSection.NormalizerFixedSpace

/-!
# Original fixed subgroups and general-field Cartan axes

A nonidentity element of the actual alpha centralizer is sent injectively
into the paired natural module. Its conjugation equivariance then puts an
odd subgroup of the original Hall image into one coordinate kernel. The
Cartan calculation then applies to alpha itself. Its fixed-space dimension
is derived from the original moved-alpha order by coprime splitting.
The general odd-Hall fixed-center calculation is also re-exported here,
with the actual marked pair quotient and both original factor formulas.
The general-field context now also constructs the paired section, seed
decomposition and exchanger, discharging them in the original Hall fixed-center
application. The H-star action and its comparison component are now constructed
over arbitrary even fields. Odd-order fixed-center detection eliminates both
local fixed centers and applies the common characteristic pair to that same
component, retaining its localV and generation identities. The general-field natural marking now supplies faithful odd Hall action on
the Sylow omega-center, discharging the seed-centralizer identity. The resulting
fixed-center vanishing also removes the paired coordinate kernel and places
alpha in the original module. Hall containment remains the earlier source input.

The moving-Hall assembly owner must still construct the torus markings,
and obtain the earlier-source moved-alpha order.
These are applications on the literal original subgroups, not assertions
that the terminal block or overcomponent has been constructed.
Source: Aschbacher–Smith 10.2.3(4), printed pp.746–747.
-/

public section
open Matrix Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]

/-- The actual alpha centralizer places an original odd Hall subgroup on
one of the natural coordinate kernels, over any field of characteristic two. -/
theorem source_original_odd_axis_of_alpha_fixed
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (C P : Subgroup G) (hCR : C ≤ localOrbit T L)
    (q₁ q₂ : C →* SL(2,F))
    (m : D.moduleSubgroup →* Multiplicative ((Fin 2 → F) × (Fin 2 → F)))
    (hm : Function.Injective m)
    (he : ∀ (p : C) (v : D.moduleSubgroup),
      (m ⟨(p:G)*v*(p:G)⁻¹,
        (mem_normalizer_iff.mp (D.orbit_normalizes_module (hCR p.property)) v).mp v.property⟩).toAdd =
      ((q₁ p).val *ᵥ (m v).toAdd.1, (q₂ p).val *ᵥ (m v).toAdd.2))
    (hαU : thompsonAlpha (T : Subgroup G) ≤ D.moduleSubgroup)
    (hPC : P ≤ C) (hPB : P ≤ B.map H.subtype)
    (hfixed : thompsonAlpha (T : Subgroup G) ⊓ centralizer (P : Set G) ≠ ⊥) :
    P ≤ q₁.ker.map C.subtype ∨ P ≤ q₂.ker.map C.subtype := by
  obtain ⟨⟨x,hx⟩,hne'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfixed
  have hne : x ≠ 1 := fun h => hne' (Subtype.ext h)
  let v : D.moduleSubgroup := ⟨x,hαU hx.1⟩
  have hv : (m v).toAdd ≠ 0 := by
    intro h
    have hh0 : m v = 1 := h
    have hh : m v = m 1 := hh0.trans m.map_one.symm
    exact hne (congrArg Subtype.val (hm hh))
  have hodd' : Odd (Nat.card (P.subgroupOf C)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv]
    exact c.odd_card_of_le_hall_image P hPB
  have hfix : ∀ p ∈ P.subgroupOf C,
      ((q₁ p).val *ᵥ (m v).toAdd.1, (q₂ p).val *ᵥ (m v).toAdd.2) = (m v).toAdd := by
    intro p hp
    have hcP : (p:G)*x*(p:G)⁻¹ = x := by
      rw [hx.2 p hp, mul_inv_cancel_right]
    have hh := he p v
    have hv' : (⟨(p:G)*v*(p:G)⁻¹,
        (mem_normalizer_iff.mp (D.orbit_normalizes_module (hCR p.property)) v).mp v.property⟩ :
        D.moduleSubgroup) = v := Subtype.ext hcP
    rw [hv'] at hh
    exact hh.symm
  rcases SL2.PairedOddAxes.le_kernel_or_le_kernel_of_nonzero_fixed
    q₁ q₂ (P.subgroupOf C) hodd' (m v).toAdd hv hfix with hq | hq
  · left
    intro p hp
    exact mem_map.mpr ⟨⟨p,hPC hp⟩,hq hp,rfl⟩
  · right
    intro p hp
    exact mem_map.mpr ⟨⟨p,hPC hp⟩,hq hp,rfl⟩

local instance originalAlphaElementary :
    IsElementaryAbelian 2 (thompsonAlpha (T : Subgroup G)) :=
  omegaOneCenterAmbient_elementaryAbelian _

local instance originalAlphaFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The source fixed-dimension identity on the actual alpha subgroup forces
the selected Cartan torus to have full degree and equal an original axis. -/
theorem source_original_cartan_axis_of_fixed_dimension [Finite F]
    (C P : Subgroup G)
    (hCα : C ≤ normalizer (thompsonAlpha (T : Subgroup G) : Set G))
    (q₁ q₂ : C →* Fˣ) (hq : Function.Bijective (fun d => (q₁ d, q₂ d)))
    (a : Additive (thompsonAlpha (T : Subgroup G)) ≃ₗ[ZMod 2] F × F)
    (he : ∀ (d : C) (x : thompsonAlpha (T : Subgroup G)),
      a (Additive.ofMul ((thompsonAlpha (T : Subgroup G)).normalizerMonoidHom
        (inclusion hCα d) x)) =
          ((q₁ d : F) * (a (Additive.ofMul x)).1,
           (q₂ d : F) * (a (Additive.ofMul x)).2))
    (hPC : P ≤ C) [IsCyclic P]
    (m n : ℕ) (hm : 1 < m) (hF : Nat.card F = 2 ^ n)
    (hP : Nat.card P = 2 ^ m - 1)
    (hdim : Module.finrank (ZMod 2)
      (fixedSpace (BinaryConjugationSection.originalNormalizerAction hCα)
        (P.subgroupOf C)) = 2*n-m) :
    m = n ∧ (P = q₂.ker.map C.subtype ∨ P = q₁.ker.map C.subtype) :=
  cartan_axis_of_paired_torus C P (thompsonAlpha (T : Subgroup G)) hCα
    q₁ q₂ hq a he hPC m n hm hF hP hdim

/-- The actual alpha-centralizer order gives the Cartan-axis conclusion,
using the literal conjugation fixed space rather than a dimension callback. -/
theorem source_original_cartan_axis_of_centralizer_order [Finite F]
    (C P : Subgroup G)
    (hCα : C ≤ normalizer (thompsonAlpha (T : Subgroup G) : Set G))
    (q₁ q₂ : C →* Fˣ) (hq : Function.Bijective (fun d => (q₁ d, q₂ d)))
    (a : Additive (thompsonAlpha (T : Subgroup G)) ≃ₗ[ZMod 2] F × F)
    (he : ∀ (d : C) (x : thompsonAlpha (T : Subgroup G)),
      a (Additive.ofMul ((thompsonAlpha (T : Subgroup G)).normalizerMonoidHom
        (inclusion hCα d) x)) =
          ((q₁ d : F) * (a (Additive.ofMul x)).1,
           (q₂ d : F) * (a (Additive.ofMul x)).2))
    (hPC : P ≤ C) [IsCyclic P]
    (m n : ℕ) (hm : 1 < m) (hF : Nat.card F = 2 ^ n)
    (hP : Nat.card P = 2 ^ m - 1)
    (hcard : Nat.card (thompsonAlpha (T : Subgroup G) ⊓ centralizer (P : Set G) : Subgroup G) =
      2 ^ (2*n-m)) :
    m = n ∧ (P = q₂.ker.map C.subtype ∨ P = q₁.ker.map C.subtype) := by
  have hdim := BinaryConjugationSection.finrank_originalFixedSpace_of_card
    hCα P hPC (2*n-m) hcard
  exact source_original_cartan_axis_of_fixed_dimension C P hCα q₁ q₂ hq a he
    hPC m n hm hF hP hdim

/-- The source moved-alpha order supplies the fixed-dimension input by
coprime splitting. The actor is a subgroup of the original odd Hall image. -/
theorem source_original_cartan_axis_of_moved_order [Finite F]
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (C P : Subgroup G)
    (hCα : C ≤ normalizer (thompsonAlpha (T : Subgroup G) : Set G))
    (q₁ q₂ : C →* Fˣ) (hq : Function.Bijective (fun d => (q₁ d, q₂ d)))
    (a : Additive (thompsonAlpha (T : Subgroup G)) ≃ₗ[ZMod 2] F × F)
    (he : ∀ (d : C) (x : thompsonAlpha (T : Subgroup G)),
      a (Additive.ofMul ((thompsonAlpha (T : Subgroup G)).normalizerMonoidHom
        (inclusion hCα d) x)) =
          ((q₁ d : F) * (a (Additive.ofMul x)).1,
           (q₂ d : F) * (a (Additive.ofMul x)).2))
    (hPC : P ≤ C) (hPB : P ≤ B.map H.subtype) [IsCyclic P]
    (m n : ℕ) (hm : 1 < m) (hF : Nat.card F = 2 ^ n)
    (hP : Nat.card P = 2 ^ m - 1)
    (hmoved : Nat.card (⁅thompsonAlpha (T : Subgroup G),P⁆ : Subgroup G) = 2 ^ m) :
    m = n ∧ (P = q₂.ker.map C.subtype ∨ P = q₁.ker.map C.subtype) := by
  let E := thompsonAlpha (T : Subgroup G)
  have hE : Nat.card E = 2 ^ (2*n) := by
    calc
      Nat.card E = Nat.card (F × F) := Nat.card_congr a.toEquiv
      _ = 2^n * 2^n := by rw [Nat.card_prod,hF]
      _ = 2^(2*n) := by rw [two_mul,pow_add]
  have hn : P ≤ normalizer (E : Set G) := hPC.trans hCα
  have hcop : Nat.Coprime (Nat.card P) (Nat.card E) := by
    rw [hE]
    exact (ctx.odd_card_of_le_hall_image P hPB).coprime_two_right.pow_right (2*n)
  have hmn : m ≤ 2*n := by
    have hME : ⁅E,P⁆ ≤ E := le_normalizer_iff_commutator_le_left.mp hn
    have hle := Nat.card_le_card_of_injective (inclusion hME) (inclusion_injective hME)
    rw [hmoved,hE] at hle
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
  have hcard := centralizer_card_of_binary_moved_order E P hn hcop m (2*n-m)
    (by rw [Nat.add_sub_of_le hmn]; exact hE) hmoved
  exact source_original_cartan_axis_of_centralizer_order C P hCα q₁ q₂ hq a he
    hPC m n hm hF hP hcard

end CFSG.Quasithin.Chapter10.MovingHall
