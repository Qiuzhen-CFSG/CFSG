module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.FullAction
public import Theory.SpecificGroups.OrthogonalFourBinary.SingularLineDisplacement

/-!
# The line residual on the natural four-space

Residual functoriality identifies the actual image of `Y_E` with the
coordinate line residual. Its surjective displacement proves `V=[V,Y_E]`.
Its faithful restriction to the line identifies `C_{Y_E}(E)` with
`C_{Y_E}(V)`. The earlier `O₂(Y)=C_Y(V)` makes this kernel a two-group;
the cubic image forces every normal two-subgroup into it. Hence it is
exactly `O₂(Y_E)`, with an explicit intrinsic action-kernel equality.

Only the earlier action-image conclusion of 15.3.7 and the kernel conclusion
of 15.3.49(3) are used. In particular no conclusion of 15.3.67 is required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7, 15.3.49(3), and 15.3.66(5), printed pp.1122, 1142 and 1152.
-/

@[expose] public section

open Subgroup OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
open GoldschmidtCore.LocalRelations GoldschmidtCore.LocalRelations.OrthogonalProducts
variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G}

/-- On the line residual, fixing the line pointwise is equivalent to fixing all of `V`. -/
theorem lineY_centralizer_line_eq_module (d : NaturalAction V M) (Y E : Subgroup G)
    (hYM : Y ≤ M) (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (himage : actionImage d Y = pResidual 2 IsometryGroup) :
    lineY Y E ⊓ centralizer (E : Set G) = lineY Y E ⊓ centralizer (V : Set G) := by
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    let m : M := ⟨x,hYM ((lineY_le Y E).trans inf_le_left hx)⟩
    have hg : d.action m ∈ lineResidual (coordinateLine d E) := by
      rw [← actionImage_lineY d Y E hYM hEV himage]
      exact mem_map_of_mem _ hx
    have he := lineResidual_faithful_on_line (coordinateLine d E)
      ((coordinateLine_card d E hEV).trans hcard) (coordinateLine_singular d E hEV hs)
      (d.action m) hg (by
        intro w
        apply d.coordinates.symm.injective
        apply Subtype.ext
        have hh := d.intertwines m (d.coordinates.symm w.val)
        rw [d.coordinates.apply_symm_apply] at hh
        exact hh.trans (mul_inv_eq_iff_eq_mul.mpr
          (mem_centralizer_iff.mp hc _ ((mem_coordinateLine d E _).mp w.property)).symm))
    have hm : m ∈ d.action.ker := he
    rw [action_ker d] at hm
    exact ⟨hx,hm⟩
  · exact inf_le_inf_left _ (centralizer_le hEV)

/-- Source 15.3.66(5): the residual line stabilizer generates all displacement in `V`. -/
theorem lineY_commutator (d : NaturalAction V M) (Y E : Subgroup G)
    (hYM : Y ≤ M) (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (himage : actionImage d Y = pResidual 2 IsometryGroup) :
    V = ⁅V,lineY Y E⁆ := by
  apply le_antisymm
  · obtain ⟨g,hg,hmove⟩ := lineResidual_displacement_surjective (coordinateLine d E)
      ((coordinateLine_card d E hEV).trans hcard) (coordinateLine_singular d E hEV hs)
    rw [← actionImage_lineY d Y E hYM hEV himage] at hg
    obtain ⟨m,hm,rfl⟩ := hg
    intro v hv
    obtain ⟨w,hw⟩ := hmove (d.coordinates ⟨v,hv⟩)
    let a := d.coordinates.symm w
    have hconj := d.intertwines m a
    rw [d.coordinates.apply_symm_apply] at hconj
    have he := congrArg (fun u => (d.coordinates.symm u : G)) hw
    rw [map_mul, map_inv, d.coordinates.symm_apply_apply, Subgroup.coe_mul, Subgroup.coe_inv] at he
    change (d.coordinates.symm (vectorAction (d.action m) w) : G) * (a : G)⁻¹ = v at he
    change (d.coordinates.symm (vectorAction (d.action m) w) : G) =
      (m : G) * (a : G) * (m : G)⁻¹ at hconj
    rw [hconj] at he
    have hvcomm : v = ⁅(m : G),(a : G)⁆ := by
      exact he.symm
    rw [hvcomm, commutator_comm V (lineY Y E)]
    exact commutator_mem_commutator hm a.property
  · exact le_normalizer_iff_commutator_le_left.mp
      ((lineY_le Y E).trans (inf_le_left.trans (hYM.trans d.normalizes)))

/-- Every cube in `Y_E` acts trivially on `V`. -/
theorem lineY_cube_centralizes_module (d : NaturalAction V M) (Y E : Subgroup G)
    (hYM : Y ≤ M) (hEV : E ≤ V)
    (himage : actionImage d Y = pResidual 2 IsometryGroup)
    (y : G) (hy : y ∈ lineY Y E) : y ^ 3 ∈ centralizer (V : Set G) := by
  let m : M := ⟨y, hYM ((lineY_le Y E).trans inf_le_left hy)⟩
  have hg : d.action m ∈ lineResidual (coordinateLine d E) := by
    rw [← actionImage_lineY d Y E hYM hEV himage]
    exact mem_map_of_mem _ hy
  have hk : m ^ 3 ∈ d.action.ker := by
    change d.action (m ^ 3) = 1
    rw [map_pow]
    exact lineResidual_cube _ _ hg
  rw [action_ker d] at hk
  exact hk

/-- The kernel of the specified action of `Y_E` on `V` is its intrinsic two-core. -/
theorem lineY_action_ker_eq_twoCore (d : NaturalAction V M) (Y E : Subgroup G)
    (hYM : Y ≤ M) (hEV : E ≤ V)
    (himage : actionImage d Y = pResidual 2 IsometryGroup)
    (hYcore : Stellmacher.twoCoreAmbient Y = Y ⊓ centralizer (V : Set G)) :
    (d.action.comp (inclusion ((lineY_le Y E).trans (inf_le_left.trans hYM)))).ker =
      pCore 2 (lineY Y E) := by
  let A := lineY Y E
  have hAY : A ≤ Y := (lineY_le Y E).trans inf_le_left
  let f : A →* IsometryGroup := d.action.comp (inclusion (hAY.trans hYM))
  have hk : f.ker = (centralizer (V : Set G)).subgroupOf A := by
    ext a
    change inclusion (hAY.trans hYM) a ∈ d.action.ker ↔ _
    rw [action_ker d]
    rfl
  have hCY : IsPGroup 2 (Y ⊓ centralizer (V : Set G) : Subgroup G) := by
    rw [← hYcore]
    exact pCore_isPGroup.map Y.subtype
  have hker : IsPGroup 2 f.ker := by
    rw [hk]
    exact (hCY.comap_subtype (K := A)).to_le (fun a ha => ⟨hAY a.property,ha⟩)
  change f.ker = pCore 2 A
  have hle : f.ker ≤ pCore 2 A := le_sSup ⟨inferInstance,hker⟩
  apply le_antisymm hle
  intro a ha
  have hcube : f a ^ 3 = 1 := by
    have hc := lineY_cube_centralizes_module d Y E hYM hEV himage a a.property
    have hh : a ^ 3 ∈ f.ker := hk.symm ▸ hc
    simpa only [MonoidHom.mem_ker, map_pow] using hh
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)) ⟨a,ha⟩
  have hpow : f a ^ 2 ^ n = 1 := by
    have hh := congrArg f (congrArg Subtype.val hn)
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using hh
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 2 3).pow_left n)
    (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one hcube))

/-- The ambient form of the action-kernel equality. -/
theorem lineY_twoCore (d : NaturalAction V M) (Y E : Subgroup G)
    (hYM : Y ≤ M) (hEV : E ≤ V)
    (himage : actionImage d Y = pResidual 2 IsometryGroup)
    (hYcore : Stellmacher.twoCoreAmbient Y = Y ⊓ centralizer (V : Set G)) :
    Stellmacher.twoCoreAmbient (lineY Y E) = lineY Y E ⊓ centralizer (V : Set G) := by
  have h := lineY_action_ker_eq_twoCore d Y E hYM hEV himage hYcore
  have hk : (d.action.comp (inclusion ((lineY_le Y E).trans (inf_le_left.trans hYM)))).ker =
      (centralizer (V : Set G)).subgroupOf (lineY Y E) := by
    ext a
    change inclusion _ a ∈ d.action.ker ↔ _
    rw [action_ker d]
    rfl
  change (pCore 2 (lineY Y E)).map (lineY Y E).subtype = _
  rw [← h, hk, subgroupOf_map_subtype, inf_comm]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
