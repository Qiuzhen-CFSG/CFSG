module

public import Stellmacher.Recognition.NormalFourOddCoreSetup

/-!
# Excluding a moving conjugate of the unique normal four

Let `W` be the unique normal elementary four of a Sylow two-subgroup `S`,
with `|Ω₁(Z(S))| = 2`. If its image in `N/O₂′(N)` is normal, where
`N = N_G(Ω₁(Z(S)))`, every conjugate of `W` contained in `S` equals `W`.

The elementary rank bound gives a short transport proof. Every four in `S`
contains its central omega. Consequently, the conjugate of `C_S(W)` lies in
`N`, and an element of `N` carries it into `S`. Its image has index two in
`S` and centralizes the transported four. Under the rank bound, that four
is normal in `S`, hence equals `W` by uniqueness. Normality of the quotient
image then undoes the transport inside `N` without changing `W`.

This proves the moving-conjugate contradiction needed in both fusion cases
of Janko–Thompson, Math. Z. 113 (1970), §6, p.395 (using §§3.1–3.2 in the
source). The stronger elementary rank bound used here permits the direct
argument above. No existence theorem for a moving conjugate, simplicity,
solvability, or ambient classification is used.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo
open Subgroup

/-- A conjugate returning to the Sylow fixes the unique normal four when its
odd-core quotient image is normal. -/
public theorem conjugate_four_eq_of_normal_fourImage
    {G : Type*} [Group G] [Finite G]
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    [(fourImage S E).Normal]
    (g : G)
    (hconj : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G)) :
    (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
      E.map (S : Subgroup G).subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let W := E.map (S : Subgroup G).subtype
  let V := W.map (MulAut.conj g).toMonoidHom
  let C := centralizer (E : Set S)
  let K := (C.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom
  let N := omegaNormalizer S
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hVcard : Nat.card V = 4 := by
    rw [card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective (S : Subgroup G).subtype_injective, hE]
  have hZV : centralOmega S ≤ V := by
    let F := V.subgroupOf (S : Subgroup G)
    let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hconj
    have hFcard : Nat.card F = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe hconj).toEquiv).trans hVcard
    have h := centralOmega_le_four hrank S F hFcard
    rwa [map_subgroupOf_eq_of_le hconj] at h
  have hVK : V ≤ K := map_mono (map_mono E.le_centralizer)
  have hKC : K ≤ centralizer (V : Set G) := by
    rintro x ⟨a, ⟨c, hc, rfl⟩, rfl⟩ y ⟨b, ⟨e, he, rfl⟩, rfl⟩
    simpa only [Subgroup.coe_mul, map_mul, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply] using
      congrArg (fun s : S => (MulAut.conj g) (s : G)) (hc e he)
  have hKN : K ≤ N :=
    (hKC.trans (centralizer_le hZV)).trans (Subgroup.centralizer_le_normalizer _)
  let KN := K.subgroupOf N
  have hKp : IsPGroup 2 K := ((S.isPGroup'.to_subgroup C).map _).map _
  have hKNp : IsPGroup 2 KN := hKp.comap_subtype
  obtain ⟨T, hKT⟩ := hKNp.exists_le_sylow
  let SN := S.subtype (sylow_le_omegaNormalizer S)
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N T SN
  have htrans : KN.map (MulAut.conj n).toMonoidHom ≤ (SN : Subgroup N) := by
    rw [← hn]
    exact map_mono hKT
  let R := K.map (MulAut.conj (n : G)).toMonoidHom
  let F := V.map (MulAut.conj (n : G)).toMonoidHom
  have hRS : R ≤ (S : Subgroup G) := by
    rintro x ⟨k, hk, rfl⟩
    exact htrans (mem_map_of_mem (MulAut.conj n).toMonoidHom
      (show (⟨k, hKN hk⟩ : N) ∈ KN from hk))
  have hFR : F ≤ R := map_mono hVK
  have hFS : F ≤ (S : Subgroup G) := hFR.trans hRS
  have hRF : R ≤ centralizer (F : Set G) := by
    rintro x ⟨k, hk, rfl⟩ y ⟨v, hv, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj (n : G)) (hKC hk v hv)
  let RS := R.subgroupOf (S : Subgroup G)
  let FS := F.subgroupOf (S : Subgroup G)
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 FS := IsElementaryAbelian.subgroupOf hFS
  have hRcard : Nat.card RS = Nat.card C := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRS).toEquiv,
      card_map_of_injective (MulAut.conj (n : G)).injective,
      card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective (S : Subgroup G).subtype_injective]
  have hRindex : RS.index = 2 := by
    have hc := C.card_mul_index
    rw [centralizer_index_two S hZ E hE] at hc
    have hr := RS.card_mul_index
    rw [hRcard] at hr
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := C)) (hr.trans hc.symm)
  let : RS.Normal := normal_of_index_eq_two hRindex
  have hFcard : Nat.card FS = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hFS).toEquiv,
      card_map_of_injective (MulAut.conj (n : G)).injective, hVcard]
  have hFn : FS.Normal := normal_four_of_normal_centralizing_overgroup
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) FS RS hFcard
    (fun _ hx => hFR hx) (fun x hx y hy => Subtype.ext (hRF hx y hy))
  have hFE : FS = E := hunique FS hFn inferInstance hFcard
  have hFW : F = W := by
    change F.subgroupOf (S : Subgroup G) = E at hFE
    rw [← map_subgroupOf_eq_of_le hFS, hFE]
  have hback : W.map (MulAut.conj ((n : G)⁻¹)).toMonoidHom = V := by
    rw [← hFW, map_map]
    have hid : (MulAut.conj ((n : G)⁻¹)).toMonoidHom.comp
        (MulAut.conj (n : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [mul_assoc]
    rw [hid, map_id]
  have heq := conjugate_four_eq_of_mem_omegaNormalizer S E (n : G)⁻¹
    (N.inv_mem n.property) (hback ▸ hconj)
  exact hback.symm.trans heq

/-- The distinct moving conjugate supplied by the ambient fusion argument
cannot exist under the rank bound and normal quotient-image hypothesis. -/
public theorem false_of_distinct_conjugate_four
    {G : Type*} [Group G] [Finite G]
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    [(fourImage S E).Normal]
    (g : G)
    (hconj : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hne : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠
      E.map (S : Subgroup G).subtype) : False :=
  hne (conjugate_four_eq_of_normal_fourImage hrank S hZ E hE hunique g hconj)

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
