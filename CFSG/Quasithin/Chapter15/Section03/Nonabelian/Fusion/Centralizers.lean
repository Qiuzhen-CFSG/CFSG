module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Constructions
public import Theory.GroupTheory.SaturatedCentralizerTransport
public import Theory.GroupTheory.NormalFourCentralizerSeparation

/-!
# The centralizer deductions in 15.3.60–61

Normalizer control promotes a local Sylow group in `C_M(D_M)` to one in
`C_G(D_M)`: the center of its dihedral two-group is the involution whose
full centralizer lies in `M`. Conjugating `D_M` to `D_H` would then put a
two-group of order 16 inside a centralizer with Sylow two-group of order 8.
Sylow conjugacy inside element centralizers deduces the two involution
nonfusion assertions from this subgroup separation.

The local centralizer structures, the Sylow three-groups, and the existence
of a conjugate of `D_H` centralized by `t` remain explicit inputs. In
particular, the quotient fixed-coset calculation from the natural/dual
decomposition is not replaced by assuming nonfusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion
variable {G : Type*} [Group G]

/-- Ambient conjugacy of the subgroups, with an actual conjugator. -/
def SubgroupConjugate (D E : Subgroup G) : Prop :=
  ∃ g : G, D.map (MulAut.conj g).toMonoidHom = E

theorem SubgroupConjugate.symm {D E : Subgroup G} (h : SubgroupConjugate D E) :
    SubgroupConjugate E D := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

theorem SubgroupConjugate.trans {D E F : Subgroup G}
    (hDE : SubgroupConjugate D E) (hEF : SubgroupConjugate E F) :
    SubgroupConjugate D F := by
  obtain ⟨g, rfl⟩ := hDE
  obtain ⟨h, rfl⟩ := hEF
  refine ⟨h * g, ?_⟩
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_centralizer (D : Subgroup G) (f : G ≃* G) :
    (centralizer (D : Set G)).map f.toMonoidHom =
      centralizer (D.map f.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    intro y hy
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using hx (f y) (mem_map_of_mem _ hy)

/-- The local Sylow two-subgroup of `C_M(D_M)` remains Sylow in
`C_G(D_M)` when its central involution has full centralizer in `M`. -/
theorem centralizer_sylow_of_center_involution [Finite G]
    (M D P : Subgroup G) (v : G) (hv : orderOf v = 2)
    (hP : IsPGroup 2 P) (hPD : P ≤ centralizer (D : Set G))
    (hlocal : ¬ 2 ∣ P.relIndex (M ⊓ centralizer (D : Set G)))
    (hcenter : (center P).map P.subtype = zpowers v)
    (hcontrol : centralizer ({v} : Set G) ≤ M) :
    ∃ S : Sylow 2 (centralizer (D : Set G)),
      (S : Subgroup (centralizer (D : Set G))).map
        (centralizer (D : Set G)).subtype = P := by
  have hN := normalizer_le_centralizer_of_characteristic_involution
    P (center P) v hv hcenter
  have hmax := not_dvd_relIndex_of_normalizer_inf_le P
    (M ⊓ centralizer (D : Set G)) (centralizer (D : Set G)) hP hPD hlocal
    (le_inf (inf_le_left.trans (hN.trans hcontrol)) inf_le_right)
  refine ⟨(hP.comap_subtype : IsPGroup 2
    (P.subgroupOf (centralizer (D : Set G)))).toSylow hmax, ?_⟩
  exact map_subgroupOf_eq_of_le hPD

/-- A larger prime subgroup in the second centralizer obstructs subgroup conjugacy.
Only the first centralizer needs a full Sylow subgroup. -/
theorem not_subgroupConjugate_of_centralizer_card [Finite G]
    {p : ℕ} [Fact p.Prime] (D E R : Subgroup G)
    (P : Sylow p (centralizer (D : Set G)))
    (hR : IsPGroup p R) (hRE : R ≤ centralizer (E : Set G))
    (hsmall : Nat.card P < Nat.card R) : ¬ SubgroupConjugate D E := by
  rintro ⟨g, hg⟩
  have hc : Nat.card (centralizer (D : Set G)) = Nat.card (centralizer (E : Set G)) := by
    rw [← hg, ← map_centralizer, card_map_of_injective (MulAut.conj g).injective]
  obtain ⟨Q, hQ⟩ :=
    (hR.comap_subtype : IsPGroup p (R.subgroupOf (centralizer (E : Set G)))).exists_le_sylow
  have hcardQ : Nat.card Q = Nat.card P := by
    rw [Q.card_eq_multiplicity, P.card_eq_multiplicity, hc]
  have hle := card_le_of_le hQ
  change Nat.card (R.subgroupOf (centralizer (E : Set G))) ≤ Nat.card Q at hle
  rw [Nat.card_congr (subgroupOfEquivOfLe hRE).toEquiv, hcardQ] at hle
  exact hsmall.not_ge hle

/-- Sylow conjugacy inside an element centralizer turns element fusion into
conjugacy of equal-order prime subgroups that centralize those elements. -/
theorem not_isConj_of_centralizing_subgroups [Finite G]
    {p : ℕ} [Fact p.Prime] (D E : Subgroup G) (t z : G)
    (P : Sylow p (centralizer ({z} : Set G)))
    (hPE : (P : Subgroup (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype = E)
    (hD : IsPGroup p D) (hcard : Nat.card D = Nat.card E)
    (hDt : D ≤ centralizer ({t} : Set G))
    (hsep : ¬ SubgroupConjugate D E) : ¬ IsConj t z := by
  have hE : IsPGroup p E := hPE ▸ P.isPGroup'.map _
  have hEz : E ≤ centralizer ({z} : Set G) := hPE ▸ map_subtype_le _
  have hmax (W : Subgroup G) (hW : IsPGroup p W) (hEW : E ≤ W)
      (hWz : W ≤ centralizer ({z} : Set G)) : W = E := by
    have hPW : (P : Subgroup (centralizer ({z} : Set G))) ≤
        W.subgroupOf (centralizer ({z} : Set G)) := by
      intro x hx
      exact hEW (hPE ▸ mem_map_of_mem _ hx)
    have he := P.is_maximal' hW.comap_subtype hPW
    have hm := congrArg (fun A : Subgroup (centralizer ({z} : Set G)) =>
      A.map (centralizer ({z} : Set G)).subtype) he
    calc
      W = (W.subgroupOf (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype := (map_subgroupOf_eq_of_le hWz).symm
      _ = _ := hm
      _ = E := hPE
  intro hconj
  obtain ⟨g, _, hle⟩ := exists_conj_into_saturated_centralizer z t E D
    hE hD hEz hDt hmax hconj
  exact hsep ⟨g, eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective (MulAut.conj g).injective, hcard])⟩

/-- The deductions of 15.3.60 and 15.3.61(1) from the local centralizer
calculations. The order-eight versus order-sixteen comparison proves the
subgroup separation; both involution nonfusion assertions are then derived. -/
theorem nonfusion_of_local_centralizers [Finite G]
    (DM DH R : Subgroup G) (t z v : G)
    (PM : Sylow 2 (centralizer (DM : Set G)))
    (hPM : Nat.card PM = 8) (hR : IsPGroup 2 R)
    (hRcard : Nat.card R = 16) (hRDH : R ≤ centralizer (DH : Set G))
    (Pz : Sylow 3 (centralizer ({z} : Set G)))
    (hPz : (Pz : Subgroup (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype = DH)
    (Pv : Sylow 3 (centralizer ({v} : Set G)))
    (hPv : (Pv : Subgroup (centralizer ({v} : Set G))).map
      (centralizer ({v} : Set G)).subtype = DM)
    (hDM : Nat.card DM = 3) (hDH : Nat.card DH = 3)
    (htM : DM ≤ centralizer ({t} : Set G))
    (htH : ∃ g : G, DH.map (MulAut.conj g).toMonoidHom ≤ centralizer ({t} : Set G)) :
    ¬ SubgroupConjugate DM DH ∧ ¬ IsConj t z ∧ ¬ IsConj t v := by
  have hsep := not_subgroupConjugate_of_centralizer_card DM DH R PM hR hRDH
    (by omega)
  have hDMp : IsPGroup 3 DM := IsPGroup.of_card (n := 1) (by simpa using hDM)
  have hDHp : IsPGroup 3 DH := IsPGroup.of_card (n := 1) (by simpa using hDH)
  refine ⟨hsep, not_isConj_of_centralizing_subgroups DM DH t z Pz hPz
    hDMp (hDM.trans hDH.symm) htM hsep, ?_⟩
  obtain ⟨g, hg⟩ := htH
  refine not_isConj_of_centralizing_subgroups
    (DH.map (MulAut.conj g).toMonoidHom) DM t v Pv hPv (hDHp.map _) ?_ hg ?_
  · rw [card_map_of_injective (MulAut.conj g).injective, hDM, hDH]
  · intro h
    exact hsep ((SubgroupConjugate.trans ⟨g, rfl⟩ h).symm)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion
