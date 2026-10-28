module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Center.Coprime

/-!
# Natural coordinates of the Sylow-center displacement

The natural quotient U(L)/C_U(L) carries the marked SL₂ action. A vector
fixed by the root group has second coordinate zero. Consequently the
Sylow-center displacement embeds in the first coordinate: coprime action
makes its intersection with the kernel C_U(L) trivial. The diagonal torus
acts on this coordinate with weight u, not the root group's weight u².

Source: Aschbacher–Smith E.6.7, printed p.246, and the natural-module
convention in C.1.12, p.124. The covering theorem I.2.3 is needed only to
show that this displacement is nonzero, not for the coordinate computation.
-/

@[expose] public section

open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.L2Torus
variable {L F : Type*} [Group L] [Field F] {B : Subgroup L}

/-- The literal projection from U(L) to its marked natural quotient. -/
def MarkedBlockModel.naturalMap (a : MarkedBlockModel L B F) :
    ChapterC.blockU L →* Multiplicative (Fin 2 → F) :=
  a.model.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (ChapterC.blockFixed L))

theorem MarkedBlockModel.naturalMap_surjective (a : MarkedBlockModel L B F) :
    Function.Surjective a.naturalMap :=
  a.model.moduleIso.surjective.comp (QuotientGroup.mk'_surjective _)

theorem MarkedBlockModel.naturalMap_eq_one (a : MarkedBlockModel L B F)
    (v : ChapterC.blockU L) : a.naturalMap v = 1 ↔ (v : L) ∈ center L := by
  change a.model.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L) v) = 1 ↔ _
  rw [map_eq_one_iff _ a.model.moduleIso.injective]
  exact QuotientGroup.eq_one_iff v

theorem MarkedBlockModel.naturalMap_conjugate (a : MarkedBlockModel L B F)
    (l : L) (v : ChapterC.blockU L) :
    (a.naturalMap (ChapterC.blockConjugate L l v)).toAdd =
      (a.linearMap l).val *ᵥ (a.naturalMap v).toAdd :=
  congrArg Multiplicative.toAdd (a.model.intertwining l v)

/-- The preimage in U(L) of the upper root-fixed line. No assertion that its
preimage is fixed is built into this definition. -/
def MarkedBlockModel.rootLine (a : MarkedBlockModel L B F) : Subgroup L :=
  (({ toFun := fun v => Multiplicative.ofAdd ((a.naturalMap v).toAdd 1)
      map_one' := by simp
      map_mul' := by intros; simp } : ChapterC.blockU L →* Multiplicative F).ker).map
    (ChapterC.blockU L).subtype

theorem MarkedBlockModel.mem_rootLine (a : MarkedBlockModel L B F) (v : L) :
    v ∈ a.rootLine ↔ ∃ hv : v ∈ ChapterC.blockU L,
      (a.naturalMap ⟨v, hv⟩).toAdd 1 = 0 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.property, hu⟩
  · rintro ⟨hv, he⟩
    exact ⟨⟨v, hv⟩, he, rfl⟩

variable [Finite F] [CharP F 2]

theorem MarkedBlockModel.naturalMap_second_eq_zero (a : MarkedBlockModel L B F)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) (v : ChapterC.blockU L)
    (hv : (v : L) ∈ centralizer (S : Set L)) :
    (a.naturalMap v).toAdd 1 = 0 := by
  obtain ⟨s, hs⟩ := a.linearMap_surjective
    (transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F))
  have hsS : s ∈ (S : Subgroup L) := by
    rw [a.sylow_eq_root_comap S hS]
    change a.linearMap s ∈ upperUnipotent F
    rw [hs]
    exact (mem_upperUnipotent F _).mpr ⟨1, rfl⟩
  have he : ChapterC.blockConjugate L s v = v := by
    apply Subtype.ext
    change s * (v : L) * s⁻¹ = v
    rw [mem_centralizer_iff.mp hv s hsS, mul_inv_cancel_right]
  have hcoord := congrFun (a.naturalMap_conjugate s v) 0
  rw [he, hs] at hcoord
  simpa [transvection_coe, mulVec, dotProduct, Fin.sum_univ_two] using hcoord.symm

theorem MarkedBlockModel.blockU_centralizer_sylow_le_rootLine (a : MarkedBlockModel L B F)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    ChapterC.blockU L ⊓ centralizer (S : Set L) ≤ a.rootLine := by
  intro v hv
  exact (a.mem_rootLine v).mpr
    ⟨hv.1, a.naturalMap_second_eq_zero S hS ⟨v, hv.1⟩ hv.2⟩

variable {a : MarkedBlockModel L B F}

/-- The displacement subgroup has its canonical first-coordinate homomorphism. -/
noncomputable def DiagonalSection.displacementCoordinate (d : DiagonalSection a)
    (hshort : ChapterC.IsShort L) (S : Sylow 2 L) :
    ↥⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ →* Multiplicative F :=
  { toFun := fun v => Multiplicative.ofAdd
      ((a.naturalMap (inclusion (d.displacement_le_blockU hshort S) v)).toAdd 0)
    map_one' := by simp
    map_mul' := by intros; simp }

theorem DiagonalSection.displacementCoordinate_injective [Finite L]
    (d : DiagonalSection a) (hshort : ChapterC.IsShort L)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    Function.Injective (d.displacementCoordinate hshort S) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro v hv
  have hZ := d.displacement_le_omegaCenter S hS v.property
  have hvS := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hZ
  have hzero := a.naturalMap_second_eq_zero S hS
    (inclusion (d.displacement_le_blockU hshort S) v) (mem_centralizer_iff.mpr hvS.2.2)
  have hcent : (v : L) ∈ center L := by
    apply (a.naturalMap_eq_one (inclusion (d.displacement_le_blockU hshort S) v)).mp
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact hv
    · exact hzero
  apply mem_bot.mpr
  apply Subtype.ext
  exact disjoint_def.mp (d.omegaCenter_center_disjoint S hS hn hF) ⟨hZ, hcent⟩ v.property

omit [Finite F] [CharP F 2] in
/-- The scalar weight of the moving line is u itself. -/
theorem DiagonalSection.displacementCoordinate_conjugate (d : DiagonalSection a)
    (hshort : ChapterC.IsShort L) (S : Sylow 2 L)
    (x : d.torus) (v : ↥⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆) :
    (d.displacementCoordinate hshort S
      ((⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆).normalizerMonoidHom
        (inclusion (normalizer_commutator_ge_right _ _) x) v)).toAdd =
      (d.torusEquiv x : F) * (d.displacementCoordinate hshort S v).toAdd := by
  have he := congrFun (a.naturalMap_conjugate (x : L)
    (inclusion (d.displacement_le_blockU hshort S) v)) 0
  rw [d.quotient_torusEquiv] at he
  have hc : inclusion (d.displacement_le_blockU hshort S)
      ((⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆).normalizerMonoidHom
        (inclusion (normalizer_commutator_ge_right _ _) x) v) =
      ChapterC.blockConjugate L (x : L)
        (inclusion (d.displacement_le_blockU hshort S) v) := by
    apply Subtype.ext
    rfl
  change (a.naturalMap _).toAdd 0 = _
  rw [hc]
  simpa [displacementCoordinate, diag2_coe', mulVec, dotProduct, Fin.sum_univ_two] using he

end CFSG.Quasithin.ChapterE.Section06.L2Torus
