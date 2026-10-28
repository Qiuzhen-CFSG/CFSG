module

public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.PCoreFrattiniAction

/-!
# Prime cores modulo their Frattini subgroups

If G/O_p(G) is a q-group and O_q(G) is trivial, the p-complement core
embeds in the q-group quotient and is therefore trivial. Solvable Fitting
self-centralization then makes O_p(G) self-centralizing.

For any self-centralizing p-core P, the quotient by the image of Φ(P) has
trivial q-core for q ≠ p. Its normal q-core commutes with the image of P,
so its preimage acts trivially on P/Φ(P). The Burnside--Frattini action
kernel is P, and the two coprime images intersect trivially.

This is the finite-group structural argument used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, Proposition E.5.1, printed p.242.
-/

namespace Subgroup

variable {X : Type*} [Group X] [Finite X]

/-- A prime core with prime-power quotient is self-centralizing if the latter
prime core of the ambient group is trivial. -/
public theorem centralizer_pCore_le_of_quotient_isPGroup
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hcore : pCore q X = ⊥) (hq : IsPGroup q (X ⧸ pCore p X)) :
    centralizer (pCore p X : Set X) ≤ pCore p X := by
  let P := pCore p X
  let T := pPrimeCore p X
  let f := (QuotientGroup.mk' P).comp T.subtype
  have hdis : Disjoint T P := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := X)).exists_card_eq
    change Nat.Coprime (Nat.card (pPrimeCore p X)) (Nat.card (pCore p X))
    rw [hn]
    exact (pPrimeCore_coprime_card (p := p) (G := X)).symm.pow_right n
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    exact mem_bot.mp (hdis.le_bot ⟨x.property, (QuotientGroup.eq_one_iff _).mp hx⟩)
  have hT : T = ⊥ := by
    apply bot_unique
    calc T ≤ pCore q X := le_sSup ⟨inferInstance, hq.of_injective f hinj⟩
         _ = ⊥ := hcore
  have hfit := Fitting_eq_pcore X p hT
  let : Group.IsNilpotent P := (pCore_isPGroup (p := p) (G := X)).isNilpotent
  let : Group.IsNilpotent (X ⧸ P) := hq.isNilpotent
  have hsolvP : Group.IsSolvable P := inferInstance
  have hsolvQ : Group.IsSolvable (X ⧸ P) := inferInstance
  have hsolv : Group.IsSolvable X :=
    (Group.isSolvable_iff_subgroup_quotient P).mpr ⟨hsolvP, hsolvQ⟩
  rw [← hfit]
  exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv

/-- For a self-centralizing p-core, factoring out its embedded Frattini
subgroup leaves trivial q-core for every prime q distinct from p. -/
public theorem pCore_quotient_frattini_pCore_eq_bot
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hc : centralizer (pCore p X : Set X) ≤ pCore p X) :
    let N := (frattini (pCore p X)).map (pCore p X).subtype
    pCore q (X ⧸ N) = ⊥ := by
  let P := pCore p X
  let N := (frattini P).map P.subtype
  let π := QuotientGroup.mk' N
  let D := pCore q (X ⧸ N)
  have hdis : Disjoint (P.map π) D :=
    IsPGroup.disjoint_of_ne p q hpq _ _ (pCore_isPGroup.map π) pCore_isPGroup
  have hnormal : (P.map π).Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective N)
  have hcomm : ⁅P.map π, D⁆ = ⊥ :=
    bot_unique ((commutator_le_inf _ _).trans hdis.le_bot)
  let action := (quotientAut (frattini P)).comp (MulAut.conjNormal : X →* MulAut P)
  have hker : action.ker = P := pCore_frattini_action_kernel p hc
  have hpre : D.comap π ≤ P := by
    intro x hx
    rw [← hker, MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) v
    change quotientAut (frattini P) (MulAut.conjNormal x)
      (QuotientGroup.mk' (frattini P) y) = QuotientGroup.mk' (frattini P) y
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hxy : π (x * (y : X) * x⁻¹) = π (y : X) := by
      have he := (commutator_eq_bot_iff_le_centralizer.mp hcomm)
        (mem_map_of_mem π y.property)
      have heq := mem_centralizer_iff.mp he (π x) hx
      simpa only [map_mul, map_inv] using mul_inv_eq_of_eq_mul heq
    have hmem : x * (y : X) * x⁻¹ / (y : X) ∈ N :=
      QuotientGroup.eq_iff_div_mem.mp hxy
    obtain ⟨z, hz, he⟩ := hmem
    have he' : z = (MulAut.conjNormal x) y / y := Subtype.ext he
    exact he' ▸ hz
  have hle : D ≤ P.map π := by
    rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) D]
    exact map_mono hpre
  exact bot_unique ((le_inf hle le_rfl).trans hdis.le_bot)

end Subgroup
