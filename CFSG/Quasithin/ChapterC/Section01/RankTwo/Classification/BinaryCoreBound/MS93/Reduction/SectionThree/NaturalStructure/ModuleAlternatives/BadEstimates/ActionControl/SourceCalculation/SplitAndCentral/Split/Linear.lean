module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.ModuleCriterion
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.FieldTheory.Finiteness

/-!
# Pointwise fixers on two simultaneous natural binary modules

For an order-four subgroup of SL₃(2), a fixed codimension at most two on
N ⊕ N forces its common fixed space on N to be a plane. The binary quotient
by that plane has just one nonzero vector, so every matrix fixing the plane
has all its displacements in the plane. Evaluation at a vector outside the
plane distinguishes the four group elements; hence those displacements fill
the plane. Applying this independently in the two coordinates identifies the
actual commutator with the four-dimensional common fixed space.

The final theorem is the finite pointwise-fixer calculation for the doubled
natural branch of Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of
rank two* (1993), (3.2)(iii), p.863, and (3.3), pp.866–868. Both copies use the
same matrix. The ambient critical-pair transport and quotient-displacement
assembly are separate. The order and codimension assumptions already imply
the intermediate identities without needing elementary abelianness.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Split.Linear
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
local notation "N" => Fin 3 → ZMod 2
local notation "V" => Fin 2 → N
local notation "natRep" => specialLinearNatural (k := ZMod 2) 3
local notation "rho" => AbelianCore.DoubleCopy.natural

private def fixedCopiesEquiv (E : Subgroup SL) :
    fixedSpace rho E ≃ₗ[ZMod 2] (Fin 2 → fixedSpace natRep E) where
  toFun v i := ⟨v.val i, fun e => congrFun (v.property e) i⟩
  invFun v := ⟨fun i => v i, fun e => funext fun i => (v i).property e⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem fixedCopies_finrank (E : Subgroup SL) :
    Module.finrank (ZMod 2) (fixedSpace rho E) =
      2 * Module.finrank (ZMod 2) (fixedSpace natRep E) := by
  rw [(fixedCopiesEquiv E).finrank_eq, Module.finrank_pi_fintype]
  simp

private theorem natRep_ext {g h : SL} (he : ∀ v, natRep g v = natRep h v) : g = h := by
  apply Matrix.SpecialLinearGroup.toLin'_injective
  ext v i
  exact congrFun (he v) i

private theorem fixedPlane_finrank (E : Subgroup SL) (hcard : Nat.card E = 4)
    (hcodim : fixedCodim rho E ≤ 2) :
    Module.finrank (ZMod 2) (fixedSpace natRep E) = 2 := by
  have hd := (fixedSpace rho E).finrank_quotient_add_finrank
  have hV : Module.finrank (ZMod 2) V = 6 := by
    simp [Module.finrank_pi_fintype]
  change fixedCodim rho E + Module.finrank (ZMod 2) (fixedSpace rho E) = _ at hd
  rw [fixedCopies_finrank, hV] at hd
  have hle := (fixedSpace natRep E).finrank_le
  have hN : Module.finrank (ZMod 2) N = 3 := by simp
  rw [hN] at hle
  by_contra hn
  have heq : Module.finrank (ZMod 2) (fixedSpace natRep E) = 3 := by omega
  have htop : fixedSpace natRep E = ⊤ := Submodule.eq_top_of_finrank_eq (heq.trans hN.symm)
  have : Subsingleton E := ⟨fun a b => Subtype.ext (natRep_ext fun v => by
    have hv : v ∈ fixedSpace natRep E := by rw [htop]; trivial
    exact (hv a).trans (hv b).symm)⟩
  have hone : Nat.card E = 1 := Nat.card_unique
  omega

private theorem plane_quotient_card (W : Submodule (ZMod 2) N)
    (hW : Module.finrank (ZMod 2) W = 2) : Nat.card (N ⧸ W) = 2 := by
  have hd := W.finrank_quotient_add_finrank
  have hq : Module.finrank (ZMod 2) (N ⧸ W) = 1 := by
    simp only [hW, Module.finrank_pi, Fintype.card_fin] at hd
    omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hq, Nat.card_zmod, pow_one]

private theorem quotient_eq_of_nonzero (W : Submodule (ZMod 2) N)
    (hW : Module.finrank (ZMod 2) W = 2) {x y : N ⧸ W}
    (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (0 : N ⧸ W)).mp (plane_quotient_card W hW)
  exact (hz x hx).trans (hz y hy).symm

private theorem plane_displacement (W : Submodule (ZMod 2) N)
    (hW : Module.finrank (ZMod 2) W = 2) (g : SL)
    (hfix : ∀ w ∈ W, natRep g w = w) (v : N) : natRep g v - v ∈ W := by
  by_cases hv : v ∈ W
  · rw [hfix v hv, sub_self]
    exact W.zero_mem
  · have hgv : natRep g v ∉ W := by
      intro hg
      have he := (Matrix.SpecialLinearGroup.toLin' g).injective (hfix _ hg)
      exact hv (he ▸ hg)
    exact (Submodule.Quotient.eq W).mp
      (quotient_eq_of_nonzero W hW
        (mt (Submodule.Quotient.mk_eq_zero W).mp hgv)
        (mt (Submodule.Quotient.mk_eq_zero W).mp hv))

private theorem plane_cosets (W : Submodule (ZMod 2) N)
    (hW : Module.finrank (ZMod 2) W = 2) (x : N) (hx : x ∉ W) (v : N) :
    v ∈ W ∨ v - x ∈ W := by
  by_cases hv : v ∈ W
  · exact Or.inl hv
  · exact Or.inr ((Submodule.Quotient.eq W).mp (quotient_eq_of_nonzero W hW
      (mt (Submodule.Quotient.mk_eq_zero W).mp hv) (mt (Submodule.Quotient.mk_eq_zero W).mp hx)))

private theorem displacement_surjective (E : Subgroup SL) (hcard : Nat.card E = 4)
    (hW : Module.finrank (ZMod 2) (fixedSpace natRep E) = 2)
    (x : N) (hx : x ∉ fixedSpace natRep E) :
    ∀ w ∈ fixedSpace natRep E, ∃ e : E, natRep e x - x = w := by
  let W := fixedSpace natRep E
  let f : E → W := fun e => ⟨natRep e x - x,
    plane_displacement W hW e (fun _ hw => hw e) x⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hab' : natRep a x = natRep b x := sub_left_inj.mp (congrArg Subtype.val hab)
    apply Subtype.ext
    apply natRep_ext
    intro v
    rcases plane_cosets W hW x hx v with hv | hv
    · exact (hv a).trans (hv b).symm
    · have he := (hv a).trans (hv b).symm
      change natRep a (v - x) = natRep b (v - x) at he
      simpa only [map_sub, hab', sub_left_inj] using he
  have hCW : Nat.card W = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hW, Nat.card_zmod]
    rfl
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard.trans hCW.symm⟩).2
  intro w hw
  obtain ⟨e, he⟩ := hs ⟨w, hw⟩
  exact ⟨e, congrArg Subtype.val he⟩

private theorem rho_single (g : SL) (i : Fin 2) (v : N) :
    rho g (Pi.single i v) = Pi.single i (natRep g v) := by
  funext j
  change natRep g ((Pi.single i v : V) j) = (Pi.single i (natRep g v) : V) j
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne h]

private theorem mem_fixedCopies (E : Subgroup SL) (v : V) :
    v ∈ fixedSpace rho E ↔ ∀ i, v i ∈ fixedSpace natRep E := by
  constructor
  · intro hv i e
    exact congrFun (hv e) i
  · intro hv e
    exact funext fun i => hv i e

private theorem single_mem_fixedCopies (E : Subgroup SL) (i : Fin 2) (v : N)
    (hv : v ∈ fixedSpace natRep E) : Pi.single i v ∈ fixedSpace rho E := by
  intro e
  change rho e (Pi.single i v) = Pi.single i v
  rw [rho_single, show natRep e v = v from hv e]

/-- The doubled commutator is exactly the doubled common fixed plane. -/
theorem moved_eq_fixedSpace (E : Subgroup SL) (hcard : Nat.card E = 4)
    (hcodim : fixedCodim rho E ≤ 2) :
    subspaceCommutator rho ⊤ E = fixedSpace rho E := by
  have hW := fixedPlane_finrank E hcard hcodim
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨e, he, v, _, rfl⟩
    apply (mem_fixedCopies E _).mpr
    intro i
    exact plane_displacement (fixedSpace natRep E) hW e (fun _ hw => hw ⟨e, he⟩) (v i)
  · have hx : ∃ x : N, x ∉ fixedSpace natRep E := by
      by_contra h
      have htop : fixedSpace natRep E = ⊤ := by
        apply top_unique
        intro v _
        exact Classical.byContradiction fun hv => h ⟨v, hv⟩
      rw [htop] at hW
      norm_num at hW
    obtain ⟨x, hx⟩ := hx
    intro v hv
    have hsingle : ∀ i, Pi.single i (v i) ∈ subspaceCommutator rho ⊤ E := by
      intro i
      obtain ⟨e, he⟩ := displacement_surjective E hcard hW x hx (v i)
        ((mem_fixedCopies E v).mp hv i)
      have hm : rho e (Pi.single i x) - Pi.single i x ∈ subspaceCommutator rho ⊤ E :=
        Submodule.subset_span ⟨e, e.property, Pi.single i x, Submodule.mem_top, rfl⟩
      rw [rho_single, ← Pi.single_sub, he] at hm
      exact hm
    rw [← Finset.univ_sum_single v]
    exact Submodule.sum_mem _ fun i _ => hsingle i

/-- The common fixed space on the two natural copies has binary dimension four. -/
theorem fixedSpace_finrank (E : Subgroup SL) (hcard : Nat.card E = 4)
    (hcodim : fixedCodim rho E ≤ 2) :
    Module.finrank (ZMod 2) (fixedSpace rho E) = 4 := by
  rw [fixedCopies_finrank, fixedPlane_finrank E hcard hcodim]

/-- The commutator of the two natural copies has binary dimension four. -/
theorem moved_finrank (E : Subgroup SL) (hcard : Nat.card E = 4)
    (hcodim : fixedCodim rho E ≤ 2) :
    Module.finrank (ZMod 2) (subspaceCommutator rho ⊤ E) = 4 := by
  rw [moved_eq_fixedSpace E hcard hcodim, fixedSpace_finrank E hcard hcodim]

/-- Pointwise fixation of the actual doubled commutator forces every
natural displacement into that commutator. -/
theorem displacement_mem_of_fixes_moved (E : Subgroup SL)
    (_hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 4)
    (hcodim : fixedCodim rho E ≤ 2) (g : SL)
    (hfix : ∀ w ∈ subspaceCommutator rho ⊤ E, rho g w = w) (v : V) :
    rho g v - v ∈ subspaceCommutator rho ⊤ E := by
  have hD := moved_eq_fixedSpace E hcard hcodim
  rw [hD] at hfix ⊢
  have hplane : ∀ w ∈ fixedSpace natRep E, natRep g w = w := by
    intro w hw
    have h := congrFun (hfix (Pi.single 0 w) (single_mem_fixedCopies E 0 w hw)) 0
    rw [rho_single] at h
    simpa using h
  apply (mem_fixedCopies E _).mpr
  intro i
  exact plane_displacement _ (fixedPlane_finrank E hcard hcodim) g hplane (v i)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Split.Linear
