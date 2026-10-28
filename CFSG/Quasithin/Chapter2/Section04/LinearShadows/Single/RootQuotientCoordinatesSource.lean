module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionFusionSource

/-!
# The literal source root quotient and its order

The actual embedding R≤L maps R/O₂(H) isomorphically onto a Sylow two-subgroup
of L/O₂(L). The marked natural block quotient then gives order 2^n, for both
the centerless and full-cover cases. The quotient equivalence retains its
value on every original representative, for fixed-root lifting applications.

Source: Aschbacher–Smith, 2.4.8(3) and 2.4.12(2), printed pp.529–532.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_root_quotient_coordinates
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let N := (twoCore d.H).subgroupOf R
    let : N.Normal := source_field_core_normal d
    let hRL : R≤L := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1
    ∃ P : Sylow 2 (L ⧸ pCore 2 L), ∃ e : (R ⧸ N) ≃* P,
      ∀ r : R, (e (QuotientGroup.mk' N r) : L ⧸ pCore 2 L) =
        QuotientGroup.mk' (pCore 2 L) (inclusion hRL r) := by
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Q := twoCore d.H
  let N := Q.subgroupOf R
  let : N.Normal := source_field_core_normal d
  let hRL : R≤L := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1
  obtain ⟨P₀,hP₀⟩ := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.1
  change (P₀:Subgroup L).map L.subtype=R at hP₀
  have hRP : R.subgroupOf L = (P₀ : Subgroup L) := by
    rw [←hP₀]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  let q := QuotientGroup.mk' (pCore 2 L)
  let K := L ⧸ pCore 2 L
  let P : Sylow 2 K := P₀.mapSurjective (f:=q) (QuotientGroup.mk'_surjective _)
  let φ : R→*K := q.comp (inclusion hRL)
  have hφrange : φ.range=(P:Subgroup K) := by
    change (q.comp (inclusion hRL)).range=(P₀:Subgroup L).map q
    rw [MonoidHom.range_comp,inclusion_range,hRP]
  have hcore : (pCore 2 L).map L.subtype=Q :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hunique).2
  have hker : φ.ker=N := by
    ext r
    change q (inclusion hRL r)=1 ↔ (r:G)∈Q
    rw [show q (inclusion hRL r)=1 ↔ inclusion hRL r∈pCore 2 L from QuotientGroup.eq_one_iff _]
    have hh := (mem_map_iff_mem L.subtype_injective :
      L.subtype (inclusion hRL r)∈(pCore 2 L).map L.subtype ↔ inclusion hRL r∈pCore 2 L)
    rw [hcore] at hh
    exact hh.symm
  let e : (R ⧸ N)≃*P := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφrange))
  exact ⟨P,e,fun _ => rfl⟩

theorem source_root_quotient_card
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let N := (twoCore d.H).subgroupOf R
    let : N.Normal := source_field_core_normal d
    Nat.card (R ⧸ N)=2^n := by
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let N := (twoCore d.H).subgroupOf R
  let : N.Normal := source_field_core_normal d
  obtain ⟨P,e,he⟩ := source_root_quotient_coordinates d hG T hST hsingle hL hM hTM hunique
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  obtain ⟨F,_,_,hF,_,ρ,⟨m⟩,_⟩ := hK.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  let P' := P.mapSurjective (f:=m.quotientIso.toMonoidHom) m.quotientIso.surjective
  change Nat.card (R ⧸ N)=2^n
  calc
    Nat.card (R ⧸ N)=Nat.card P := Nat.card_congr e.toEquiv
    _=Nat.card P' := Nat.card_congr (equivMapOfInjective (P:Subgroup (L ⧸ pCore 2 L))
      m.quotientIso.toMonoidHom m.quotientIso.injective).toEquiv
    _=Nat.card F := Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P').symm.toEquiv
    _=2^n := hF


end CFSG.Quasithin.Chapter2.LinearShadows.Single
