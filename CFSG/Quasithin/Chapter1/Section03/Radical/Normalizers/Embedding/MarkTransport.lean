module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Marked

/-!
# Transport of the marked five-kernel

The chosen odd subgroup injects into the quotient by a two-core. In particular,
its actual Sylow carrier, rather than an unspecified isomorphic subgroup, has
an equivalence to its quotient image. All formulas use the original inclusion.

The marked extension property is preserved and reflected by injective maps.
Applying this to the inclusion-induced component quotient equivalence transfers
both the kernel and the SL₂(5) quotient between N/O₂(N) and K/O₂(K). No parabolic
recognition or identification of the A.3.12 kernel is assumed by these transports.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed p.513.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
universe u v
variable {G : Type u} [Group G] {H : Type v} [Group H]

private theorem subgroupOf_map_equiv {P B : Subgroup G} (hPB : P ≤ B)
    (f : G →* H) (hf : Function.Injective f) :
    (P.subgroupOf B).map (B.equivMapOfInjective f hf).toMonoidHom =
      (P.map f).subgroupOf (B.map f) := by
  apply map_injective (B.map f).subtype_injective
  rw [map_map, map_subgroupOf_eq_of_le (map_mono hPB)]
  change (P.subgroupOf B).map (f.comp B.subtype) = P.map f
  rw [← map_map, map_subgroupOf_eq_of_le hPB]

/-- Transport both the marked kernel and the quotient through an injection. -/
theorem MarkedFiveExtension.map {B P : Subgroup G} (h : MarkedFiveExtension B P)
    (f : G →* H) (hf : Function.Injective f) :
    MarkedFiveExtension (B.map f) (P.map f) := by
  obtain ⟨hPB, ⟨ep⟩, hn, ⟨eq⟩⟩ := h
  let eB := B.equivMapOfInjective f hf
  have he := subgroupOf_map_equiv hPB f hf
  let : ((P.map f).subgroupOf (B.map f)).Normal := he ▸ hn.map eB.toMonoidHom eB.surjective
  exact ⟨map_mono hPB, ⟨(P.equivMapOfInjective f hf).symm.trans ep⟩,
    inferInstance, ⟨(QuotientGroup.congr _ _ eB he).symm.trans eq⟩⟩

/-- Recover the same marked kernel and quotient from an injective image. -/
theorem MarkedFiveExtension.of_map {B P : Subgroup G}
    (f : G →* H) (hf : Function.Injective f)
    (h : MarkedFiveExtension (B.map f) (P.map f)) : MarkedFiveExtension B P := by
  obtain ⟨hPB, ⟨ep⟩, hn, ⟨eq⟩⟩ := h
  have hle : P ≤ B := by
    intro a ha
    obtain ⟨b, hb, he⟩ := hPB (mem_map_of_mem f ha)
    exact hf he ▸ hb
  let eB := B.equivMapOfInjective f hf
  have he := subgroupOf_map_equiv hle f hf
  have hc : ((P.map f).subgroupOf (B.map f)).comap eB.toMonoidHom = P.subgroupOf B := by
    rw [← he, comap_map_eq_self_of_injective eB.injective]
  let : (P.subgroupOf B).Normal := hc ▸ hn.comap eB.toMonoidHom
  exact ⟨hle, ⟨(P.equivMapOfInjective f hf).trans ep⟩,
    inferInstance, ⟨(QuotientGroup.congr _ _ eB he).trans eq⟩⟩

/-- The two-core cannot kill an element of the chosen odd subgroup. -/
theorem odd_quotient_injective {p : ℕ} (hp : Odd p) {P K : Subgroup G}
    (hPK : P ≤ K) (hP : IsPGroup p P) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hPK)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have hd : Disjoint (P.subgroupOf K) (pCore 2 K) :=
    hP.comap_subtype.disjoint_of_coprime pCore_isPGroup (Nat.coprime_two_right.mpr hp)
  have hmem : inclusion hPK a ∈ pCore 2 K := (QuotientGroup.eq_one_iff _).mp ha
  have he : inclusion hPK a = 1 := disjoint_def.mp hd a.property hmem
  exact Subtype.ext (congrArg (fun z : K => (z : G)) he)

/-- The equivalence uses the specified subgroup inclusion into K. -/
noncomputable def oddImageEquiv {p : ℕ} (hp : Odd p) {P K : Subgroup G}
    (hPK : P ≤ K) (hP : IsPGroup p P) :
    P ≃* (P.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) := by
  let f := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hPK)
  let g : P →* (P.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) :=
    f.codRestrict _ (fun a => ⟨inclusion hPK a, a.property, rfl⟩)
  apply MulEquiv.ofBijective g
  constructor
  · intro a b h
    exact odd_quotient_injective hp hPK hP (congrArg Subtype.val h)
  · rintro ⟨b, k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

/-- The image equivalence is the quotient map on every representative. -/
theorem oddImageEquiv_apply {p : ℕ} (hp : Odd p) {P K : Subgroup G}
    (hPK : P ≤ K) (hP : IsPGroup p P) (a : P) :
    (oddImageEquiv hp hPK hP a : XiQuotient K) =
      QuotientGroup.mk' (pCore 2 K) (inclusion hPK a) := rfl

/-- Retain a chosen Sylow subgroup of X, including its original carrier. -/
noncomputable def sylowImageEquiv {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {X K : Subgroup G} (hXK : X ≤ K) (P : Sylow p X) :
    P ≃* (((P : Subgroup X).map X.subtype).subgroupOf K).map
      (QuotientGroup.mk' (pCore 2 K)) :=
  ((P : Subgroup X).equivMapOfInjective X.subtype X.subtype_injective).trans
    (oddImageEquiv hp ((map_subtype_le _).trans hXK) (P.isPGroup'.map X.subtype))

/-- The chosen Sylow marking is unchanged on representatives. -/
theorem sylowImageEquiv_apply {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {X K : Subgroup G} (hXK : X ≤ K) (P : Sylow p X) (a : P) :
    (sylowImageEquiv hp hXK P a : XiQuotient K) =
      QuotientGroup.mk' (pCore 2 K) ⟨a, hXK a.val.property⟩ := rfl

/-- The marked extension in the A.3.12 quotient is exactly the marked
extension in the intrinsic component quotient used by recognition. -/
theorem markedFiveExtension_componentQuotient_iff [Finite G] {Y P K N : Subgroup G}
    (hYK : Y ≤ K) (hPK : P ≤ K) (hKN : K ≤ N) (hK : (K.subgroupOf N).IsCComponent) :
    MarkedFiveExtension ((Y.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)))
      ((P.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ↔
    MarkedFiveExtension ((Y.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)))
      ((P.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) := by
  let e := componentQuotientEquiv hKN hK
  let f := ((K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))).subtype.comp e.toMonoidHom
  have hf : Function.Injective f :=
    ((K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))).subtype_injective.comp e.injective
  have hY : ((Y.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map f =
      (Y.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)) := by
    rw [← map_map]
    exact componentQuotientEquiv_map_subgroup hYK hKN hK
  have hP : ((P.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map f =
      (P.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)) := by
    rw [← map_map]
    exact componentQuotientEquiv_map_subgroup hPK hKN hK
  constructor
  · intro h
    simpa only [hY, hP] using h.map f hf
  · intro h
    apply MarkedFiveExtension.of_map f hf
    simpa only [hY, hP] using h

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
