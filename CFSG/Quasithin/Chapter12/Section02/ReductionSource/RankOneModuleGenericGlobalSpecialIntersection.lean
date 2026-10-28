module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialIntersection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityCentralizers

/-!
# Special-core intersection bounds in the original rank-one setup

For the actual right factor K = O²(H), any conjugate core with a distinct
root center has elementary intersection with Q = O₂(K). The explicit
commutator forms bound this intersection by q³ in G₂ and q⁵ in triality,
where q = 2^n at the original exponent. The symplectic and cubic-trace
calculations work over every relevant field, including field order four.

This discharges the elementary-intersection and size step of F.4.35 in
the literal Chapter12 application. Original uniqueness in Preparation
and compatible amalgam comparison remain inputs. The centralizing root
pair and Sylow placements remain needed for nonfusion. The new point
and whole-root centralizer counts are q⁴ and q⁸, and the literal indices
|S:Q| are q and q³. Once the two source placements hold, these counts
and the intersection bounds prove S = Q C_{Q^g}(Z). No count or index
premise remains. The placements, nonfixed short-root action, exhaustive
comparison and ambient recognition remain to be completed.
The original source S, whole overlap and both orientations are retained.
Source: Aschbacher–Smith F.4.35, printed p.292, 5.3.3, p.659, and the
Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual G₂ core intersection is elementary and has order at most q^3. -/
theorem rankOne_global_g2_special_core_intersection
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse))
    (g : G) (hg : g ∉ normalizer (residual H : Set G)) :
    let Q := (residual H).pCoreIn 2
    IsElementaryAbelian 2 (Q ⊓ Q.map (MulAut.conj g).toMonoidHom : Subgroup G) ∧
      Nat.card (Q ⊓ Q.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ (2^n)^3 := by
  exact d.g2_special_core_intersection
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he g hg

/-- The actual triality core intersection is elementary and has order at most q^5. -/
theorem rankOne_global_triality_special_core_intersection
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse))
    (g : G) (hg : g ∉ normalizer (residual H : Set G)) :
    let Q := (residual H).pCoreIn 2
    IsElementaryAbelian 2 (Q ⊓ Q.map (MulAut.conj g).toMonoidHom : Subgroup G) ∧
      Nat.card (Q ⊓ Q.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ (2^n)^5 := by
  exact d.triality_special_core_intersection
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he g hg

/-- Exact point and placed whole-root centralizer counts in the original G₂ core. -/
theorem rankOne_global_g2_special_core_centralizers
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse)) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    (∀ x ∈ Q, x ∉ Z → Nat.card (Q ⊓ centralizer ({x} : Set G) : Subgroup G)=(2^n)^4) ∧
    (∀ g : G, g ∉ normalizer (residual H : Set G) →
      Z ≤ Q.map (MulAut.conj g).toMonoidHom →
      Nat.card (Q.map (MulAut.conj g).toMonoidHom ⊓ centralizer (Z : Set G) : Subgroup G)=(2^n)^4) := by
  exact d.g2_special_core_centralizers
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he

/-- Exact point and placed whole-root centralizer counts in the original triality core. -/
theorem rankOne_global_triality_special_core_centralizers
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    (∀ x ∈ Q, x ∉ Z → Nat.card (Q ⊓ centralizer ({x} : Set G) : Subgroup G)=(2^n)^8) ∧
    (∀ g : G, g ∉ normalizer (residual H : Set G) →
      Z ≤ Q.map (MulAut.conj g).toMonoidHom →
      Nat.card (Q.map (MulAut.conj g).toMonoidHom ⊓ centralizer (Z : Set G) : Subgroup G)=(2^n)^8) := by
  exact d.triality_special_core_centralizers
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

/-- The literal source index and product conclusion after the two F.4.35 placements,
with every order and intersection bound discharged by the G₂ comparison. -/
theorem rankOne_global_g2_special_core_saturation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse))

    (g : G) (hg : g ∉ normalizer (residual H : Set G))
    (hZQ : (center (residual H)).map (residual H).subtype ≤
      ((residual H).pCoreIn 2).map (MulAut.conj g).toMonoidHom)
    (hRS : ((residual H).pCoreIn 2).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ Global.sourceS L H) :
    let Q := (residual H).pCoreIn 2
    Q.relIndex (Global.sourceS L H)=(2^n)^1 ∧
    Global.sourceS L H = Q ⊔ (Q.map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G)) := by
  exact d.g2_special_core_saturation
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he g hg hZQ hRS

/-- The literal source index and product conclusion after the two F.4.35 placements,
with every order and intersection bound discharged by the triality comparison. -/
theorem rankOne_global_triality_special_core_saturation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse))

    (g : G) (hg : g ∉ normalizer (residual H : Set G))
    (hZQ : (center (residual H)).map (residual H).subtype ≤
      ((residual H).pCoreIn 2).map (MulAut.conj g).toMonoidHom)
    (hRS : ((residual H).pCoreIn 2).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ Global.sourceS L H) :
    let Q := (residual H).pCoreIn 2
    Q.relIndex (Global.sourceS L H)=(2^n)^3 ∧
    Global.sourceS L H = Q ⊔ (Q.map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G)) := by
  exact d.triality_special_core_saturation
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he g hg hZQ hRS

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
