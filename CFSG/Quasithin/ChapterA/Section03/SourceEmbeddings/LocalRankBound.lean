module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients

/-!
# Transporting proper local-component rank bounds

Restrict to the actual full Sylow intersection in the containing C-component,
then transport the smaller subgroup to the given model. A bound on its proper
local components contradicts the marked rank. Keeping the transport abstract
avoids elaborating the concrete model's group operations at every inclusion.
Source: the containing-component replacement in A.3.12, printed p.48.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite H] in
/-- A proper local component of a C-component generates a proper subgroup
with the marking Sylow. -/
theorem local_sup_ne_top_of_ne_top (htop : (⊤ : Subgroup H).IsCComponent)
    (S : Sylow 2 H) (D : Subgroup H) (hd : D ∈ localCComponents S)
    (hproper : D ≠ ⊤) : D ⊔ (S : Subgroup H) ≠ ⊤ := by
  intro he
  change (D.subgroupOf (D ⊔ (S : Subgroup H))).IsCComponent at hd
  rw [he] at hd
  exact hproper (le_antisymm le_top
    (subgroupOf_eq_top.mp (htop.eq_top_of_isCComponent hd)))

/-- A proper local rank bound on an actual model rules out a proper inclusion
of the original marked local component. -/
theorem eq_of_model_proper_local_primeRank_bound
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (p : ℕ) (hr : 2 ≤ primeRank p B) (e : L ≃* H)
    (hbound : (⊤ : Subgroup H).IsCComponent →
      ∀ (S : Sylow 2 H) (D : Subgroup H),
        D ∈ localCComponents S → D ≠ ⊤ → primeRank p D ≤ 1) : B = L := by
  by_contra hne
  obtain ⟨S, _, hlocal⟩ := exists_local_sylow_restriction T hB hBL hL.subnormal
  let D := (B.subgroupOf L).map e.toMonoidHom
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hd : D ∈ localCComponents ((S : Subgroup L).map e.toMonoidHom) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker
      (B := B.subgroupOf L) (S := (S : Subgroup L)) hlocal e.toMonoidHom
  have htop : (⊤ : Subgroup H).IsCComponent := by
    have hh : (⊤ : Subgroup L).IsCComponent := by
      simpa only [subgroupOf_self] using hL.subgroupOf le_rfl
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hh.map_equiv e
  have hproper : D ≠ ⊤ := by
    intro he
    have hb : B.subgroupOf L = ⊤ := by
      apply map_injective (f := e.toMonoidHom) e.injective
      simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using he
    exact hne (le_antisymm hBL (subgroupOf_eq_top.mp hb))
  have hb := hbound htop (S.mapSurjective (f := e.toMonoidHom) e.surjective) D hd hproper
  let d : B ≃* D :=
    (subgroupOfEquivOfLe hBL).symm.trans (e.subgroupMap (B.subgroupOf L))
  rw [← primeRank_equiv p d] at hb
  omega

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
