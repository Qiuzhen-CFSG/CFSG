module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.Involutions
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.GroupTheory.PerfectCentralCoverRank
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Centers of the selected component lifts

The full A.2.1 implication supplies SQTK inheritance for quasisimple sections.
The only numerical information consumed from I.1.3 is that the multiplier of
a nonabelian simple SQTK group has order dividing 48: every entry in that
table (including the noncyclic order-48 entry) has this property. Universality
maps that multiplier onto the center of a perfect cover. The odd kernel in
B.5.2 and O₂(G)=1 eliminate the even part of the center.

The explicit universal inputs have producers `qt-a-02` and `qt-i-01`.
This argument uses no A.3.18 residual alternative or model comparison.
Source: Aschbacher–Smith, A.2.1(2), p.33, I.1.1–3, p.407,
and B.5.2/B.5.7, pp.103–106, combined manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction
open ChapterA.Section02
universe u

/-- The entire earlier A.2.1 theorem, with its semisimple-section hypotheses. -/
def SemisimpleInput (K : GroupClass.{u}) : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], TheoremA K H

/-- Precisely the numerical corollary consumed from I.1.3. All six entries
have order dividing 48; this does not impose cyclicity on the multiplier. -/
def MultiplierInput (K : GroupClass.{u}) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S] [Group.IsPerfect S] [IsSimpleGroup S],
    IsSQTK K S → Nat.card (schurMultiplier S) ∣ 48

private theorem quasisimple_semisimple (H : Type u) [Group H] [IsQuasisimple H] :
    IsSemisimple H := by
  apply top_unique
  exact le_sSup (show IsComponent H ⊤ from
    ⟨(inferInstance : (⊤ : Subgroup H).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv topEquiv.symm⟩)

/-- A.2.1 applies to a quasisimple quotient of an actual subgroup of an SQTK group. -/
theorem quasisimple_section_sqtk {K : GroupClass.{u}} (hA : SemisimpleInput K)
    {H S : Type u} [Group H] [Finite H] [Group S] [Finite S] [IsQuasisimple S]
    (hH : IsSQTK K H) (hs : IsSectionOf S H) : IsSQTK K S :=
  ⟨(hA H).stronglyQuasithin_section hH.stronglyQuasithin hH.isKGroup hs
    (quasisimple_semisimple S), hs.isKGroup hH.isKGroup⟩

private theorem center_card_dvd_multiplier (M : Type u) [Group M] [Finite M]
    [Group.IsPerfect M] : Nat.card (center M) ∣ Nat.card (schurMultiplier (M ⧸ center M)) := by
  let S := M ⧸ center M
  let f : Cover M S := {
    toMonoidHom := QuotientGroup.mk' (center M)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := by rw [QuotientGroup.ker_mk'] }
  obtain ⟨h, hh, _⟩ := (universalCover_isUniversal (G := S)) M f
  have hsurj : Function.Surjective h :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      f.toMonoidHom h (hh ▸ (universalCover S).surjective) f.ker_le_center
  let k : schurMultiplier S →* center M := {
    toFun x := ⟨h x, by
      apply (QuotientGroup.eq_one_iff _).mp
      change f.toMonoidHom (h x) = 1
      exact (DFunLike.congr_fun hh (x : UniversalGroup S)).trans x.property⟩
    map_one' := Subtype.ext h.map_one
    map_mul' := fun x y => Subtype.ext (h.map_mul x y) }
  apply card_dvd_of_surjective k
  intro z
  obtain ⟨x, hx⟩ := hsurj z
  have hker : x ∈ schurMultiplier S := by
    change (universalCover S).toMonoidHom x = 1
    rw [← hh]
    change QuotientGroup.mk' (center M) (h x) = 1
    rw [hx]
    exact (QuotientGroup.eq_one_iff _).mpr z.property
  exact ⟨⟨x, hker⟩, Subtype.ext hx⟩

private theorem center_odd_of_twoCore_eq_bot (M : Type u) [Group M] [Finite M]
    (h2 : pCore 2 M = ⊥) : Odd (Nat.card (center M)) := by
  by_contra hodd
  have hd : 2 ∣ Nat.card (center M) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center M) 2 hd
  let X := (zpowers z).map (center M).subtype
  have hXc : X ≤ center M := map_subtype_le _
  let : X.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hXc hx) g, mul_inv_cancel_right]
    exact hx⟩
  have hXp : IsPGroup 2 X := by
    apply IsPGroup.of_card (n := 1)
    simp only [X, card_map_of_injective (center M).subtype_injective,
      Nat.card_zpowers, hz, pow_one]
  have hle : X ≤ pCore 2 M := le_sSup ⟨inferInstance, hXp⟩
  have hz1 : (z : M) = 1 := by
    exact (h2 ▸ hle) (mem_map_of_mem _ (mem_zpowers z))
  have : z = 1 := Subtype.ext hz1
  simp [this] at hz

/-- Every component of this odd-kernel cover has trivial two-core. -/
theorem lift_twoCore_eq_bot {K : GroupClass.{u}} {G : Type u} [Group G] [Finite G]
    (c : PreparedCover K G) (h2 : pCore 2 G = ⊥)
    {M : Subgroup c.Cover} (hM : IsComponent c.Cover M) : pCore 2 M = ⊥ := by
  have hc : pCore 2 c.Cover = ⊥ := by
    have hle : pCore 2 c.Cover ≤ c.projection.ker := by
      rw [← MonoidHom.comap_bot]
      exact map_le_iff_le_comap.mp ((c.map_pCore 2).trans h2).le
    have ho : Odd (Nat.card (pCore 2 c.Cover)) :=
      c.kernel_odd.of_dvd_nat (card_dvd_of_le hle)
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := c.Cover)).exists_card_eq
    apply (eq_bot_iff_card _).mpr
    rw [hn] at ho ⊢
    have hn0 : n = 0 := by
      by_contra hn0
      exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr (dvd_pow_self 2 hn0))
    simp [hn0]
  rw [pCore_subnormal_eq_comap 2 hM.1, hc, MonoidHom.comap_bot]
  exact (MonoidHom.ker_eq_bot_iff M.subtype).mpr M.subtype_injective

/-- I.1.3, A.2.1 and the genuine odd presentation give the required center bound. -/
theorem lift_center_order {K : GroupClass.{u}} (hA : SemisimpleInput K)
    (hI : MultiplierInput K) {G : Type u} [Group G] [Finite G]
    (c : PreparedCover K G) (h2 : pCore 2 G = ⊥)
    {M : Subgroup c.Cover} (hM : IsComponent c.Cover M) :
    Nat.card (center M) = 1 ∨ Nat.card (center M) = 3 := by
  let := hM.2
  let S := M ⧸ center M
  let : IsSimpleGroup S := IsQuasisimple.simple
  let : IsQuasisimple S := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center M)) (QuotientGroup.mk'_surjective _)
  have hs : IsSQTK K S := quasisimple_section_sqtk hA c.sqtk
    (IsSectionOf.quotient_subgroup M (center M))
  have hd : Nat.card (center M) ∣ 48 := (center_card_dvd_multiplier M).trans (hI S hs)
  have ho := center_odd_of_twoCore_eq_bot M (lift_twoCore_eq_bot c h2 hM)
  have h3 : Nat.card (center M) ∣ 3 :=
    (Nat.Coprime.dvd_mul_left (show Nat.Coprime (Nat.card (center M)) 16 from
      (Nat.coprime_two_right.mpr ho).pow_right 4)).mp (by simpa using hd)
  exact (Nat.dvd_prime Nat.prime_three).mp h3

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction
