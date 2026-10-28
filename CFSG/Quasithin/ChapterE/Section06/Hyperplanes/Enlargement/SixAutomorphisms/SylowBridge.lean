module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.FixedSpaces
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow

/-!
# The Sylow bridge for the further enlargement

The normalizer argument in E.6.5 works for every subspace of corank below m;
escape of its centralizer is unnecessary. Thus Q = C_T(V) is Sylow in C_G(B).
If Y is normal in C_G(A₁) and A₁ ≤ B, conjugation inside C_G(B) preserves Y.
A Sylow subgroup of Y centralized by B can therefore be conjugated into Q,
producing a Sylow subgroup of Y centralized by V.

This supplies the terminal bridge in E.6.23 without identifying C_M(B) with
C_G(B), and without the residual containment asserted in the printed proof.
The only residual input is the proved small-corank statement for C_M(B).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.5 and the
last paragraph on printed p.254 (PDF p.265). The bridge is a Sylow-conjugacy
replacement for that paragraph's disputed residual step.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- The common Sylow subgroup Q works even when C_G(B) does not escape M. -/
theorem smallCentralizer_sylow [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {B : Subgroup G} (hBV : B ≤ V) (hc : subgroupCorank V B < localM V) :
    ∃ S : Sylow 2 (centralizer (B : Set G)),
      (S : Subgroup (centralizer (B : Set G))).map
        (centralizer (B : Set G)).subtype = sylowCentralizer (T : Subgroup G) V := by
  let Q := sylowCentralizer (T : Subgroup G) V
  have hQp : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  have hQH : Q ≤ centralizer (B : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hBV)
  have hQr : IsPGroup 2 (Q.subgroupOf (centralizer (B : Set G))) := hQp.comap_subtype
  obtain ⟨S, hS⟩ := hQr.exists_le_sylow
  refine ⟨S, ?_⟩
  apply prime_overgroup_eq_of_normalizer_control (p := 2) Q (centralizer (B : Set G)) M
    h.normalizer_sylowCentralizer_le
  · intro P hp hQP hPH hPM
    exact h.sylowCentralizer_maximal hp hQP
      (local_two_subgroup_centralizes h hBV hc hp hPM hPH)
  · exact S.isPGroup'.map _
  · rw [← map_subgroupOf_eq_of_le hQH]
    exact map_mono hS
  · exact map_subtype_le _

private theorem sylow_transport
    {H Y Q : Subgroup G} (hn : H ≤ normalizer (Y : Set G))
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = Q)
    (P : Sylow 2 Y) (hPH : (P : Subgroup Y).map Y.subtype ≤ H) :
    ∃ P' : Sylow 2 Y, (P' : Subgroup Y).map Y.subtype ≤ Q := by
  let D := (P : Subgroup Y).map Y.subtype
  have hDp : IsPGroup 2 (D.subgroupOf H) := (P.isPGroup'.map _).comap_subtype
  obtain ⟨R, hDR⟩ := hDp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H R S
  let a : MulAut Y := Y.normalizerMonoidHom ⟨c, hn c.property⟩
  refine ⟨P.mapSurjective (f := a.toMonoidHom) a.surjective, ?_⟩
  rintro _ ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  have hzD : (z : G) ∈ D := mem_map_of_mem Y.subtype hz
  have hzR : (⟨z, hPH hzD⟩ : H) ∈ (R : Subgroup H) := hDR hzD
  have hzc : (MulAut.conj c) (⟨z, hPH hzD⟩ : H) ∈ (S : Subgroup H) := by
    rw [← hc]
    exact mem_map_of_mem (MulAut.conj c).toMonoidHom hzR
  rw [← hS]
  exact mem_map_of_mem H.subtype hzc

/-- Relative normality transports the two-central Sylow witness into C_G(V). -/
theorem exists_sylow_centralized_by_V [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {A1 B Y : Subgroup G} (h1B : A1 ≤ B) (hBV : B ≤ V)
    (hc : subgroupCorank V B < localM V)
    (hYH : Y ≤ centralizer (A1 : Set G))
    (hn : (Y.subgroupOf (centralizer (A1 : Set G))).Normal)
    (P : Sylow 2 Y)
    (hPB : (P : Subgroup Y).map Y.subtype ≤ centralizer (B : Set G)) :
    ∃ P' : Sylow 2 Y, (P' : Subgroup Y).map Y.subtype ≤ centralizer (V : Set G) := by
  obtain ⟨S, hS⟩ := smallCentralizer_sylow h hBV hc
  obtain ⟨P', hP'⟩ := sylow_transport
    ((Subgroup.centralizer_le h1B).trans ((normal_subgroupOf_iff_le_normalizer hYH).mp hn))
    S hS P hPB
  exact ⟨P', hP'.trans inf_le_right⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
