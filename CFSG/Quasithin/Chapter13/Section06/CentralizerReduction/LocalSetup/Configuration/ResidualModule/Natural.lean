module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Checked
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.NaturalCoordinates

/-!
# The natural module on the literal checked conjugate span

The ambient marking and the injective checked commutator map identify checked
Vᵥ with the binary core on three points. The genuine residual quotient is
identified with A₃ through its cubic image. Transporting the natural action
along these isomorphisms gives a faithful irreducible action, and equivariance
of the marking proves that it is precisely conjugation in C_G(v)/⟨v⟩.

`checkedNaturalData` constructs this entire output from the earlier marking
and action-kernel identity. `FlagMarking.checkedNaturalData` supplies the
actual consumer, using its own module and kernel. Rank is measured on the
binary core in the explicit equivariant identification.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.926,
with the natural-module convention of §B.3, printed p.83.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry ResidualCoordinates
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G} (s : Marking L V)

def movedAmbientMap : moved →* ↥(⁅V, Lv L (markedV s)⁆ : Subgroup G) :=
  (s.map.comp moved.subtype).codRestrict _ fun x => by
    rw [residual_commutator_eq_moved s]
    exact mem_map.mpr ⟨x, x.property, rfl⟩

noncomputable def movedAmbientEquiv : moved ≃* ↥(⁅V, Lv L (markedV s)⁆ : Subgroup G) :=
  MulEquiv.ofBijective (movedAmbientMap s) ⟨by
    intro x y h
    exact Subtype.ext (s.injective (congrArg Subtype.val h)), by
    intro x
    obtain ⟨y, hy, he⟩ := (residual_commutator_eq_moved s).le x.property
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩⟩

noncomputable def checkedMovedEquiv : moved ≃* checkedVv s :=
  (movedAmbientEquiv s).trans (checkedCommutatorEquiv s)

@[simp] theorem checkedMovedEquiv_apply (x : moved) :
    (checkedMovedEquiv s x : Gcheck (markedV s)) =
      checkedQuotientMap (markedV s) ⟨s.map x.val, module_le_Gv s (map_mem s _)⟩ := rfl

/-- The literal checked Vᵥ identified with the binary three-point core. -/
noncomputable def checkedCoreEquiv : checkedVv s ≃* Multiplicative (core (Fin 3)) :=
  (checkedMovedEquiv s).symm.trans movedCoreEquiv

@[simp] theorem checkedCoreEquiv_moved (x : moved) :
    checkedCoreEquiv s (checkedMovedEquiv s x) = movedCoreEquiv x := by
  simp [checkedCoreEquiv]

noncomputable def quotientActorEquiv (hk : s.action.ker = pCore 2 L) :
    Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s)) ≃* alternatingGroup (Fin 3) :=
  (residualQuotientEquiv s hk).trans cubicThreeEquiv

@[simp] theorem quotientActorEquiv_mk (hk : s.action.ker = pCore 2 L) (l : Lv L (markedV s)) :
    quotientActorEquiv s hk (QuotientGroup.mk' (pCore 2 (Lv L (markedV s))) l) =
      cubicThreeEquiv (residualCubicAction s l) := rfl

/-- A faithful action of the genuine quotient on the actual checked subgroup. -/
noncomputable def checkedAction (hk : s.action.ker = pCore 2 L) :
    (Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s))) →* MulAut (checkedVv s) :=
  (MulAut.congr (checkedCoreEquiv s).symm).toMonoidHom.comp
    (threeAction.comp (quotientActorEquiv s hk).toMonoidHom)

theorem checkedAction_equivariant (hk : s.action.ker = pCore 2 L)
    (q : Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s))) (x : checkedVv s) :
    checkedCoreEquiv s (checkedAction s hk q x) = Multiplicative.ofAdd
      (coreRepresentation (Fin 3) (quotientActorEquiv s hk q).val (checkedCoreEquiv s x).toAdd) := by
  change checkedCoreEquiv s ((checkedCoreEquiv s).symm
    (threeAction (quotientActorEquiv s hk q) (checkedCoreEquiv s x))) = _
  rw [MulEquiv.apply_symm_apply, threeAction_apply]

def checkedResidualMap : Lv L (markedV s) →* Gcheck (markedV s) :=
  (checkedQuotientMap (markedV s)).comp (inclusion (Lv_le_Gv _ _))

omit [Finite G] in
theorem checkedResidualMap_range : (checkedResidualMap s).range = checkedLv s := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact mem_map.mpr ⟨_, y.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem checkedMovedEquiv_conjugation (l : Lv L (markedV s)) (x : moved) :
    (checkedMovedEquiv s (movedAction (residualCubicAction s l) x) : Gcheck (markedV s)) =
      MulAut.conj (checkedResidualMap s l) (checkedMovedEquiv s x : Gcheck (markedV s)) := by
  rw [checkedMovedEquiv_apply, checkedMovedEquiv_apply]
  change checkedQuotientMap (markedV s) _ =
    checkedQuotientMap (markedV s) _ * checkedQuotientMap (markedV s) _ *
      (checkedQuotientMap (markedV s) _)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (checkedQuotientMap (markedV s))
  apply Subtype.ext
  exact (s.equivariant (inclusion (residual_le_L s) l) x.val.toAdd).symm

/-- The transported natural action is exactly ambient conjugation after
mapping both the actor and vector through the specified quotient map. -/
theorem checkedAction_conjugation (hk : s.action.ker = pCore 2 L)
    (l : Lv L (markedV s)) (x : checkedVv s) :
    (checkedAction s hk (QuotientGroup.mk' (pCore 2 (Lv L (markedV s))) l) x : Gcheck (markedV s)) =
      MulAut.conj (checkedResidualMap s l) (x : Gcheck (markedV s)) := by
  obtain ⟨y, rfl⟩ := (checkedMovedEquiv s).surjective x
  have he : checkedAction s hk (QuotientGroup.mk' (pCore 2 (Lv L (markedV s))) l)
      (checkedMovedEquiv s y) = checkedMovedEquiv s (movedAction (residualCubicAction s l) y) := by
    apply (checkedCoreEquiv s).injective
    rw [checkedAction_equivariant, quotientActorEquiv_mk, checkedCoreEquiv_moved,
      checkedCoreEquiv_moved, movedCoreEquiv_equivariant]
  rw [he]
  exact checkedMovedEquiv_conjugation s l y

theorem checkedAction_faithful (hk : s.action.ker = pCore 2 L) :
    Function.Injective (checkedAction s hk) :=
  (MulAut.congr (checkedCoreEquiv s).symm).injective.comp
    (threeAction_injective.comp (quotientActorEquiv s hk).injective)

theorem checkedAction_restrict_kernel (hk : s.action.ker = pCore 2 L) :
    ((checkedAction s hk).comp (QuotientGroup.mk' (pCore 2 (Lv L (markedV s))))).ker =
      pCore 2 (Lv L (markedV s)) := by
  rw [MonoidHom.ker_comp_of_injective _ _ (checkedAction_faithful s hk), QuotientGroup.ker_mk']

theorem checkedLv_normalizes (hk : s.action.ker = pCore 2 L) :
    checkedLv s ≤ normalizer (checkedVv s : Set (Gcheck (markedV s))) := by
  apply le_normalizer_iff.mpr
  intro l hl x hx
  obtain ⟨d, rfl⟩ := (checkedResidualMap_range s).symm ▸ hl
  have he := checkedAction_conjugation s hk d ⟨x, hx⟩
  change MulAut.conj (checkedResidualMap s d) ((⟨x, hx⟩ : checkedVv s) : Gcheck (markedV s)) ∈ checkedVv s
  rw [← he]
  exact (checkedAction s hk (QuotientGroup.mk' (pCore 2 (Lv L (markedV s))) d) ⟨x, hx⟩).property

theorem checkedAction_irreducible (hk : s.action.ker = pCore 2 L)
    (H : Subgroup (checkedVv s))
    (hH : ∀ q : Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s)),
      ∀ x ∈ H, checkedAction s hk q x ∈ H) : H = ⊥ ∨ H = ⊤ := by
  have hinv : ∀ g : alternatingGroup (Fin 3), ∀ x ∈ H.map (checkedCoreEquiv s).toMonoidHom,
      Multiplicative.ofAdd (coreRepresentation (Fin 3) g.val x.toAdd) ∈
        H.map (checkedCoreEquiv s).toMonoidHom := by
    intro g x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := (quotientActorEquiv s hk).surjective g
    exact mem_map.mpr ⟨_, hH q y hy, checkedAction_equivariant s hk q y⟩
  rcases three_irreducible _ hinv with hbot | htop
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective H (checkedCoreEquiv s).injective).mp hbot)
  · right
    apply Subgroup.map_injective (f := (checkedCoreEquiv s).toMonoidHom) (checkedCoreEquiv s).injective
    rw [htop, map_top_of_surjective _ (checkedCoreEquiv s).surjective]

/-- Natural-module data with both actual equivariance and the ambient quotient
conjugation formula. This is output data, constructed below from the marking. -/
structure CheckedNaturalData where
  actorEquiv : Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s)) ≃* alternatingGroup (Fin 3)
  vectorEquiv : checkedVv s ≃* Multiplicative (core (Fin 3))
  action : (Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s))) →* MulAut (checkedVv s)
  equivariant : ∀ q x, vectorEquiv (action q x) = Multiplicative.ofAdd
    (coreRepresentation (Fin 3) (actorEquiv q).val (vectorEquiv x).toAdd)
  conjugation : ∀ (l : Lv L (markedV s)) (x : checkedVv s),
    (action (QuotientGroup.mk' (pCore 2 (Lv L (markedV s))) l) x : Gcheck (markedV s)) =
      MulAut.conj (checkedResidualMap s l) (x : Gcheck (markedV s))
  faithful : Function.Injective action
  irreducible : ∀ H : Subgroup (checkedVv s),
    (∀ q x, x ∈ H → action q x ∈ H) → H = ⊥ ∨ H = ⊤
  rank : Module.finrank (ZMod 2) (core (Fin 3)) = 2

/-- Construct the checked natural module from exactly the earlier marking/kernel
contract, with no conclusion of 13.6 as an added premise. -/
noncomputable def checkedNaturalData (hk : s.action.ker = pCore 2 L) : CheckedNaturalData s where
  actorEquiv := quotientActorEquiv s hk
  vectorEquiv := checkedCoreEquiv s
  action := checkedAction s hk
  equivariant := checkedAction_equivariant s hk
  conjugation := checkedAction_conjugation s hk
  faithful := checkedAction_faithful s hk
  irreducible := checkedAction_irreducible s hk
  rank := three_rank

/-- Application to precisely the module and kernel carried by an aligned flag. -/
noncomputable def FlagMarking.checkedNaturalData {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (f : FlagMarking T L V V₁ V₂) : CheckedNaturalData f.module :=
  A5Module.checkedNaturalData f.module f.action_kernel

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
