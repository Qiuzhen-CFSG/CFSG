module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.NormalEightCentralizingOvergroup

/-!
# Normal quotient images without a normal elementary eight

Let `E` be the unique normal elementary four of a Sylow two-subgroup, and
assume its actual image in the central-omega normalizer modulo its odd core
is normal. A conjugate of `E` returning to the Sylow and containing central
omega equals `E`. Transport its centralizer inside the omega normalizer;
the transported four is central in a normal subgroup of index two and hence
normal by `NormalEightCentralFour`. Uniqueness identifies it, and normality
of the quotient image undoes the transport.

Unlike the rank-two transport theorem, this only bounds normal elementary
subgroups. Central-omega containment in the moving conjugate is an explicit
input: it cannot be silently inferred for nonnormal fours.

Source: Janko–Thompson, Math. Z. 113 (1970), §6, pp.395–396. This module
records a reduction; the fused moving-four and exotic order-256 arguments
remain separate prerequisites for the ambient contradiction.
-/

namespace Stellmacher.Recognition.NormalEightNormalImage

open Subgroup NormalFourCentralOmegaTwo

/-- A conjugate containing central omega equals the original normal four.
Normality is assumed only for the actual odd-core quotient image. -/
public theorem conjugate_four_eq_of_centralOmega_le
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    [(fourImage S E).Normal]
    (g : G)
    (hconj : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hcentral : centralOmega S ≤
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) :
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
  have hZV : centralOmega S ≤ V := hcentral
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
  have hFn : FS.Normal := normal_four_of_normal_centralizing_overgroup_of_no_normal_eight
    hno FS RS hFcard
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

/-- A distinct returning conjugate is disjoint from the central involution
line. In particular the rank-two central-omega containment argument cannot
be used for such a conjugate. -/
public theorem centralOmega_disjoint_of_distinct_conjugate_four
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    [(fourImage S E).Normal]
    (g : G)
    (hconj : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hne : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠
      E.map (S : Subgroup G).subtype) :
    Disjoint (centralOmega S)
      ((E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom) := by
  let Z := centralOmega S
  let V := (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom
  have hz : Nat.card Z = 2 := (card_centralOmega S).trans hZ
  have hd : Nat.card (Z ⊓ V : Subgroup G) ∣ 2 := hz ▸ card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hone | htwo
  · exact disjoint_iff.mpr (card_eq_one.mp hone)
  · have heq : Z ⊓ V = Z := eq_of_le_of_card_ge inf_le_left (by omega)
    have hZV : Z ≤ V := heq ▸ inf_le_right
    exact (hne (conjugate_four_eq_of_centralOmega_le S hno hZ E hE hunique
      g hconj hZV)).elim

/-- Two disjoint commuting ambient conjugates of a four in the Sylow
produce an intrinsic elementary sixteen containing the original four.
This is an intermediate subgroup, not a contradiction to no normal eight. -/
public theorem elementary_sixteen_of_disjoint_commuting_conjugate
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (E : Subgroup S) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) (g : G)
    (hconj : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (S : Subgroup G))
    (hdisjoint : Disjoint (E.map (S : Subgroup G).subtype)
      ((E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom))
    (hcommute : (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      centralizer (E.map (S : Subgroup G).subtype : Set G)) :
    ∃ B : Subgroup S, IsElementaryAbelian 2 B ∧ Nat.card B = 16 ∧ E ≤ B := by
  let W := E.map (S : Subgroup G).subtype
  let V := W.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (W ⊔ V : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hcommute
  have hW : Nat.card W = 4 :=
    (card_map_of_injective (S : Subgroup G).subtype_injective).trans hE
  have hV : Nat.card V = 4 :=
    (card_map_of_injective (MulAut.conj g).injective).trans hW
  have hWV : Nat.card (W ⊔ V : Subgroup G) = 16 := by
    have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes W V
      (hcommute.trans (Subgroup.centralizer_le_normalizer _))
    rw [hW, hV, disjoint_iff.mp hdisjoint, card_bot] at h
    omega
  have hWS : W ⊔ V ≤ (S : Subgroup G) := sup_le (map_subtype_le E) hconj
  let B := (W ⊔ V).subgroupOf (S : Subgroup G)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hWS
  refine ⟨B, inferInstance, ?_, ?_⟩
  · exact (Nat.card_congr (subgroupOfEquivOfLe hWS).toEquiv).trans hWV
  · intro e he
    exact (le_sup_left : W ≤ W ⊔ V) (mem_map_of_mem (S : Subgroup G).subtype he)

end Stellmacher.Recognition.NormalEightNormalImage
