module

public import Glauberman.Signalizer.SolvableQdExclusion
public import Glauberman.TheoremA
public import Glauberman.Theorem5_1
public import Glauberman.Lemma6_3
public import FeitThompson.BGsection6.Defs

/-!
# The ZJ normalizer supplements the p′-core of a solvable group

If `H` is finite and solvable, `p ≥ 5` is prime, and `S` is a Sylow
p-subgroup, then `H = O_{p′}(H) N_H(Z(J(S)))`. The ZJ subgroup is the
canonical `zjCharacteristicFunctor`, whose existing containment,
nontriviality, and injective-map naturality also apply when comparing
different local ambient groups.

The proof passes to `H/O_{p′}(H)`. Solvable Qd exclusion and Glauberman's
Lemma 6.3 give p-stability there; the solvable p-core centralizer theorem
and Theorem A make the quotient's ZJ characteristic. Naturality identifies
it with the image of ZJ(S), because the quotient map is injective on S.
The preimage L is normal and satisfies `S ∩ L = ZJ(S)`. Thus ZJ(S) is a
Sylow subgroup of L, and the Frattini argument supplies the required
normalizer supplement. No nontriviality of `O_p(H)` is assumed.

This is the ZJ version of Kurzweil–Stellmacher, *The Theory of Finite
Groups*, 9.4.6, and supplies the natural characteristic-subgroup input to
11.2.8. That application needs only the existing characteristic-functor
properties and this supplement, so it can use ZJ in place of the book's W.
-/

namespace Glauberman

/-- For a finite solvable group and a prime at least five, the normalizer of
the Sylow ZJ subgroup supplements the p′-core. -/
public theorem solvable_oddPrime_normalizer_zj_supplement
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {H : Type*} [Group H] [Finite H] (hsolv : Group.IsSolvable H)
    (S : Sylow p H) :
    pPrimeCore p H ⊔ Subgroup.normalizer
      (((zjCharacteristicFunctor p).K (S : Subgroup H) : Subgroup H) : Set H) = ⊤ := by
  classical
  let : Group.IsSolvable H := hsolv
  let M : Subgroup H := pPrimeCore p H
  let q : H →* H ⧸ M := QuotientGroup.mk' M
  let Sbar : Sylow p (H ⧸ M) := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective M)
  have hpodd : p ≠ 2 := by omega
  have hstable : pStable p (H ⧸ M) := by
    let e : ((⊤ : Subgroup (H ⧸ M)) ⧸
        (⊥ : Subgroup (⊤ : Subgroup (H ⧸ M)))) ≃* H ⧸ M :=
      QuotientGroup.quotientBot.trans Subgroup.topEquiv
    exact (pStable_iso e).mp
      ((lemma6_3 hpodd).mp (qd_not_involved_of_solvable hp inferInstance)
        (⊤ : Subgroup (H ⧸ M)) (⊥ : Subgroup (⊤ : Subgroup (H ⧸ M))))
  have hcentral : Subgroup.centralizer (pCore p (H ⧸ M) : Set (H ⧸ M)) ≤
      pCore p (H ⧸ M) :=
    centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot inferInstance
      (pPrimeCore_quotient_pPrimeCore_eq_bot (G := H) (p := p))
  let Z : Subgroup H := (zjCharacteristicFunctor p).K (S : Subgroup H)
  have hqinj : Function.Injective (q.comp (S : Subgroup H).subtype) :=
    quotient_pPrimeCore_subgroupMap_injective (S : Subgroup H) S.isPGroup'
  have hZmap : (ZJ (Sbar : Subgroup (H ⧸ M))) = Z.map q :=
    (zjCharacteristicFunctor p).K_map q (S : Subgroup H) hqinj
  have hZbarChar : (ZJ (Sbar : Subgroup (H ⧸ M))).Characteristic :=
    TheoremA.theoremA hpodd Sbar hstable hcentral
  let : (Z.map q).Normal := by
    rw [← hZmap]
    infer_instance
  let L : Subgroup H := (Z.map q).comap q
  have hLeq : L = M ⊔ Z := QuotientGroup.comap_map_mk' M Z
  have hZle : Z ≤ (S : Subgroup H) := (zjCharacteristicFunctor p).K_le _
  have hSL : (S : Subgroup H) ⊓ L = Z := by
    apply le_antisymm
    · intro x hx
      obtain ⟨z, hz, heq⟩ := hx.2
      have heq' : (⟨z, hZle hz⟩ : (S : Subgroup H)) = ⟨x, hx.1⟩ := hqinj heq
      have hzx : z = x := congrArg Subtype.val heq'
      exact hzx ▸ hz
    · intro z hz
      exact ⟨hZle hz, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩⟩
  obtain ⟨P, hP⟩ := sylow_inf_normal S (N := L)
  have hPmap : (P : Subgroup L).map L.subtype = Z := by
    rw [hP, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right, hSL]
  have hfr : Subgroup.normalizer (Z : Set H) ⊔ L = ⊤ := by
    simpa only [hPmap] using Sylow.normalizer_sup_eq_top (N := L) P
  apply top_le_iff.mp
  rw [← hfr]
  refine sup_le le_sup_right ?_
  rw [hLeq]
  exact sup_le le_sup_left (Subgroup.le_normalizer.trans le_sup_right)

end Glauberman
