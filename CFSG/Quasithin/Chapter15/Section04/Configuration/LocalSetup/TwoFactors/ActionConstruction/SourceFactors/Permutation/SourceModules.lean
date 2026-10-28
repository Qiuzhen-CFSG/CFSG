module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.SourceFactors.Permutation.SourceApplication
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.FaithfulMoved.ActionImage

/-!
# The actual four-group modules of the source residual pair

The two-residual preimage of each cubic factor has exactly that factor as
its image under the original M quotient. Restricting to X therefore gives
the literal actor-image equality for the marked faithful action. Cubic
commutator idempotence identifies its moved plane with [V(M),Lᵢ]. Thus the
same Baumann-invariant, T-exchanged pair has two actual order-four modules
whose direct product is [V(M),X].

The source application constructs the pair and every actor-image identity
from the original earlier-source input. It does not ask for abstract module
coordinates or a new pair satisfying the desired conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.4.12(6)(ii),
printed pp.1160–1161; used in the first paragraphs of 15.4.18, p.1162.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SourceFactors.Permutation.SourceModules
open FamilySource FamilySource.ModuleStructure FamilySource.ModuleStructure.BinaryNormalizer SourceApplication
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem memberProjection_image (M X L : Subgroup G) (hXM : X ≤ M) (hLX : L ≤ X) :
    ((L.subgroupOf X).map (memberProjection M X hXM)).map (image M X).subtype =
      (L.subgroupOf M).map (quotientMap M) := by
  ext a
  constructor
  · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    exact mem_map.mpr ⟨inclusion hXM x, hx, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    let x : X := ⟨(m : G), hLX hm⟩
    exact mem_map.mpr ⟨memberProjection M X hXM x, mem_map.mpr ⟨x, hm, rfl⟩, rfl⟩

/-- The residual factor has its specified image under the original quotient map. -/
theorem factor_image {T : Sylow 2 G} {M X : Subgroup G}
    (d : QuotientPair T M X) (i : Bool) :
    image M (d.factor i) = d.line i := by
  change (((residualPreimage (quotientMap M) (d.line i)).map M.subtype).comap
    M.subtype).map (quotientMap M) = d.line i
  rw [comap_map_eq_self_of_injective M.subtype_injective]
  exact residualPreimage_image (quotientMap M) (QuotientGroup.mk'_surjective _)
    (d.line i) (three_isPPerfect _ (d.card i))

/-- The literal image in the original actor X, retaining memberProjection. -/
theorem factor_actor_image {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}
    (h : Input K T M X 2) (d : QuotientPair T M X)
    (P : Bool → Subgroup (image M X))
    (hP : ∀ i, (P i).map (image M X).subtype = d.line i) (i : Bool) :
    ((d.factor i).subgroupOf X).map (memberProjection M X h.member_le) = P i := by
  have hLX : d.factor i ≤ X := by
    cases i
    · exact le_sup_left.trans_eq (d.factor_generate h)
    · exact le_sup_right.trans_eq (d.factor_generate h)
  apply map_injective (image M X).subtype_injective
  rw [memberProjection_image M X (d.factor i) h.member_le hLX, hP]
  exact factor_image d i

/-- The marked action and intrinsic planes are the actual modules of one
and the same source pair, including its Baumann and Thompson properties. -/
theorem source_marked_factor_modules {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} (h : Input K T M X 2) :
    ∃ (d : QuotientPair T M X)
      (ρ : image M X →* MulAut (movedModule (T : Subgroup G) M X)),
      Function.Injective ρ ∧
      (∀ (x : X) (w : movedModule (T : Subgroup G) M X),
        (ρ (memberProjection M X h.member_le x) w : G) =
          (x : G) * (w : G) * (x : G)⁻¹) ∧
      letI := MulDistribMulAction.compHom (movedModule (T : Subgroup G) M X) ρ
      ∃ P : FactorPair (A := image M X) (W := movedModule (T : Subgroup G) M X),
        (∀ i, (P.line i).map (image M X).subtype = d.line i) ∧
        (∀ i, ((d.factor i).subgroupOf X).map (memberProjection M X h.member_le) = P.line i) ∧
        (∀ i, (commutatorAction (P.line i) (movedModule (T : Subgroup G) M X)).map
          (movedModule (T : Subgroup G) M X).subtype = d.moduleFactor i) ∧
        (∀ i, Nat.card (d.moduleFactor i) = 4) ∧
        Disjoint (d.moduleFactor false) (d.moduleFactor true) ∧
        d.moduleFactor false ⊔ d.moduleFactor true = movedModule (T : Subgroup G) M X ∧
        (∀ i, ChapterB.baumann (T : Subgroup G) ≤ normalizer (d.factor i : Set G) ∧
          ⁅d.factor i, ChapterB.thompsonJ (T : Subgroup G) 0⁆ = d.factor i) := by
  obtain ⟨ρ, hfaith, hρ, P, hcard, hcompl, hAcard, hAinj, hgen, hperm, hnS, hnlift, hswap⟩ :=
    h.marked_double_baumann_factors
  let W := movedModule (T : Subgroup G) M X
  let _ := MulDistribMulAction.compHom W ρ
  let d : QuotientPair T M X :=
    ⟨quotientFactors M X W P, hAcard, hAinj, hgen, hperm, hswap⟩
  have hP (i : Bool) : (P.line i).map (image M X).subtype = d.line i := rfl
  have hLX (i : Bool) : d.factor i ≤ X := by
    cases i
    · exact le_sup_left.trans_eq (d.factor_generate h)
    · exact le_sup_right.trans_eq (d.factor_generate h)
  have himage (i : Bool) := factor_actor_image h d P.line hP i
  have hmodule (i : Bool) : (commutatorAction (P.line i) W).map W.subtype =
      d.moduleFactor i := h.factor_module_eq ρ hρ (d.factor i) (hLX i) (P.line i) (himage i)
  refine ⟨d, ρ, hfaith, hρ, P, hP, himage, hmodule, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← hmodule i, card_map_of_injective W.subtype_injective]
    exact hcard i
  · rw [← hmodule false, ← hmodule true]
    exact disjoint_map W.subtype_injective hcompl.disjoint
  · rw [← hmodule false, ← hmodule true, ← Subgroup.map_sup, hcompl.sup_eq_top,
      ← MonoidHom.range_eq_map, range_subtype]
  · exact fun i => ⟨hnlift i, d.factor_thompson_commutator h hnS i⟩

/-- The source-facing direct decomposition uses the actual Vi=[V(M),Li],
with order four, individual Baumann invariance and Thompson saturation. -/
theorem source_factor_modules {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} (h : Input K T M X 2) :
    ∃ d : QuotientPair T M X,
      d.factor false ⊔ d.factor true = X ∧
      (∀ i, ChapterB.baumann (T : Subgroup G) ≤ normalizer (d.factor i : Set G) ∧
        ⁅d.factor i, ChapterB.thompsonJ (T : Subgroup G) 0⁆ = d.factor i ∧
        Nat.card (⁅localV T M, d.factor i⁆ : Subgroup G) = 4) ∧
      Disjoint ⁅localV T M, d.factor false⁆ ⁅localV T M, d.factor true⁆ ∧
      ⁅localV T M, d.factor false⁆ ⊔ ⁅localV T M, d.factor true⁆ = ⁅localV T M, X⁆ := by
  obtain ⟨d, ρ, _, _, P, _, _, _, hcard, hdisj, hgen, hn⟩ := source_marked_factor_modules h
  exact ⟨d, d.factor_generate h, fun i => ⟨(hn i).1, (hn i).2, hcard i⟩,
    hdisj, hgen⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SourceFactors.Permutation.SourceModules
