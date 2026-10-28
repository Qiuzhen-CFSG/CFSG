module

public import Theory.SpecificGroups.BinaryLinear.EvenLieLevi
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Split binary higher-linear parabolics

The six-space Levi in a binary projective linear group is constructed by the
literal block action on `Space 6 × Space (d - 6)`.  The stabilizer is the
actual image of the two-block stabilizer, so its unipotent radical supplies a
proper two-local subgroup.  The first Levi factor is the literal
`PSL(6,2)` carrier.

Source: Aschbacher--Smith A.2.18, printed p.40, with the two-block
calculation of GLS3 §2.6 in `BinaryLinear.EvenLieLevi`.
-/

@[expose] public section

noncomputable section
set_option linter.style.haveILetI false
open scoped MatrixGroups
open Theory.GroupTheory
open BinaryLinear.OuterCyclic
open BinaryLinear.EvenLieLevi
namespace Theory.SpecificGroups.LinearHigher

/-- The projective linear endpoints are quasisimple over their actual fields. -/
theorem psl_isQuasisimple {F : Type*} [Field F] {n : ℕ} (hn : 3 ≤ n) :
    IsQuasisimple PSL(n,F) := by
  let := Atlas.sl_perfect (F := F) n hn
  let := Atlas.psl_simple_high_rank (F := F) n hn
  refine { simple := ?_ }
  exact ((QuotientGroup.quotientMulEquivOfEq
    (Group.IsPerfect.center_quotient_center_eq_bot SL(n,F))).trans
      QuotientGroup.quotientBot).isSimpleGroup

/-- Coordinates adapted to a `k + m` block decomposition. -/
def blockCoordinates (k m : ℕ) :
    Space (k + m) ≃ₗ[ZMod 2] Space k × Space m :=
  (LinearEquiv.piCongrLeft (ZMod 2) (fun _ => ZMod 2) finSumFinEquiv.symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin m) (ZMod 2) (ZMod 2))

/-- The ambient binary projective group in block coordinates. -/
def blockCoordinatesGroup (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    PSL(k + m, ZMod 2) ≃* BinaryLinear.GL (Space k × Space m) :=
  (projectiveEquivLinear (by omega)).trans
    (BinaryLinear.SmallParabolicLevi.linearGroupCongr
      (blockCoordinates k m))

/-- The actual projective image of the two-block stabilizer. -/
def blockParabolic (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    Subgroup PSL(k + m, ZMod 2) :=
  (BinaryLinear.parabolic (leftSpace (Space k) (Space m))).map
    (blockCoordinatesGroup k m hk hm).symm.toMonoidHom

/-- The first block, viewed inside the ambient projective group. -/
def blockFirstHom (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    PSL(k, ZMod 2) →* PSL(k + m, ZMod 2) :=
  (blockCoordinatesGroup k m hk hm).symm.toMonoidHom.comp
    ((BinaryLinear.parabolic (leftSpace (Space k) (Space m))).subtype.comp
      ((embedding (Space k) (Space m)).comp
        (((projectiveEquivLinear hk).prodCongr (projectiveEquivLinear hm)).toMonoidHom.comp
          (MonoidHom.inl (PSL(k, ZMod 2)) (PSL(m, ZMod 2))))))

/-- The block first factor is injective. -/
theorem blockFirstHom_injective (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    Function.Injective (blockFirstHom k m hk hm) := by
  intro x y hxy
  have hxy' := congrArg (blockCoordinatesGroup k m hk hm) hxy
  have hpair := embedding_injective (Space k) (Space m) (by
    simpa [blockFirstHom] using hxy')
  have hp' : (projectiveEquivLinear hk x, projectiveEquivLinear hm (1 : PSL(m, ZMod 2))) =
      (projectiveEquivLinear hk y, projectiveEquivLinear hm (1 : PSL(m, ZMod 2))) := by
    simpa using hpair
  exact (projectiveEquivLinear hk).injective (congrArg Prod.fst hp')

/-- The transported binary block parabolic is two-local. -/
theorem blockParabolic_isTwoLocal (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    IsTwoLocal (blockParabolic k m hk hm) := by
  letI : Inhabited (Fin k) := ⟨⟨0, hk⟩⟩
  letI : Inhabited (Fin m) := ⟨⟨0, hm⟩⟩
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  letI : Nontrivial (Space k) := Pi.nontrivial
  letI : Nontrivial (Space m) := Pi.nontrivial
  exact isTwoLocal_map (blockCoordinatesGroup k m hk hm).symm
    (parabolic_isTwoLocal (Space k) (Space m))

/-- The transported binary block parabolic is proper. -/
theorem blockParabolic_ne_top (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    blockParabolic k m hk hm ≠ ⊤ := by
  intro htop
  have hmap := congrArg (Subgroup.map (blockCoordinatesGroup k m hk hm).toMonoidHom) htop
  letI : Inhabited (Fin k) := ⟨⟨0, hk⟩⟩
  letI : Inhabited (Fin m) := ⟨⟨0, hm⟩⟩
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  letI : Nontrivial (Space k) := Pi.nontrivial
  letI : Nontrivial (Space m) := Pi.nontrivial
  apply parabolic_ne_top (Space k) (Space m)
  simpa [blockParabolic, Subgroup.map_map] using hmap

theorem blockFirstHom_range_le_blockParabolic (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    (blockFirstHom k m hk hm).range ≤ blockParabolic k m hk hm := by
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  refine ⟨embedding (Space k) (Space m)
    (((projectiveEquivLinear hk).prodCongr (projectiveEquivLinear hm)).toMonoidHom
      (MonoidHom.inl (PSL(k, ZMod 2)) (PSL(m, ZMod 2)) a)), ?_⟩
  exact ⟨(embedding (Space k) (Space m) _).property, rfl⟩

/-- The first factor with codomain restricted to the actual parabolic. -/
def blockFirstToParabolic (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    PSL(k, ZMod 2) →* blockParabolic k m hk hm :=
  (blockFirstHom k m hk hm).codRestrict _ (fun x =>
    blockFirstHom_range_le_blockParabolic k m hk hm ⟨x, rfl⟩)

theorem blockFirstToParabolic_injective (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    Function.Injective (blockFirstToParabolic k m hk hm) := by
  intro x y h
  exact blockFirstHom_injective k m hk hm (congrArg Subtype.val h)

end Theory.SpecificGroups.LinearHigher
end
