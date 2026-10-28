module
public import Theory.GroupAction.PrimitivePrimeTI
public import Theory.NumberTheory.BinaryPrimitiveDivisor.General
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupCartanFree
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupGeometry

/-!
# The primitive Cartan actor in the original point-TI argument

Binary Zsigmondy supplies a prime of binary order n, and the actual Cartan
of order 2ⁿ−1 contains a subgroup of that prime order. Its fixed subgroup
on the chosen natural module is trivial. The primitive-degree bound
therefore proves irreducibility on the literal point Ω₁Z(T) ∩ V.

Every point-stabilizing overgroup of this actor is irreducible too, so
its full ambient normalizer has point TI. The final theorem constructs
such an overgroup as a Sylow subgroup of C_K ∩ N_G(Z₁), retaining the
actual quotient-action kernel. It does not assert that this subgroup
is Sylow in C_K. That promotion, full residual-normalizer and global TI,
block exclusion, and final Seed assembly remain with
qt-d-1222-linear-field-parity. No Suzuki recognition premise is used here.

Source: Aschbacher–Smith 5.1.17, printed p.640 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B : Subgroup G} {n : ℕ}

theorem cartan_primitive_prime_subgroup
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hn : 1 < n) (hodd : Odd n) :
    ∃ (p : ℕ) (C : Subgroup G), p.Prime ∧ p ≠ 2 ∧
      orderOf (2 : ZMod p) = n ∧ C ≤ A ∧ Nat.card C = p := by
  obtain ⟨p,hp,hord⟩ := Theory.NumberTheory.exists_prime_orderOf_two hn
    (by intro he; subst n; exact (by decide : ¬ Odd 6) hodd)
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    simp only [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, orderOf_zero] at hord
    omega
  have hd : p ∣ 2^n-1 := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    rw [←hord,pow_orderOf_eq_one,sub_self]
  have hda : p ∣ Nat.card A := (c.left_cyclic_and_card hTL hpsl).2.symm ▸ hd
  obtain ⟨C,hC⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 1) (by simpa using hda)
  exact ⟨p,C.map A.subtype,hp,hp2,hord,map_subtype_le _,by
    rw [card_map_of_injective A.subtype_injective,hC,pow_one]⟩

/-- The chosen point has no proper nonzero subgroup invariant under the primitive actor. -/
theorem fundamental_point_primitive_irreducible
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (c : CartanPair T L H A B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : orderOf (2 : ZMod p) = n)
    (C : Subgroup G) (hCA : C ≤ A) (hC : Nat.card C = p)
    (X : Subgroup G) (hXZ : X ≤ (setup T L D.moduleSubgroup H A).V₁)
    (hCX : C ≤ normalizer (X : Set G)) :
    X = ⊥ ∨ X = (setup T L D.moduleSubgroup H A).V₁ := by
  let Z := (setup T L D.moduleSubgroup H A).V₁
  let := D.module_elementary
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_injective
    (inclusion (show Z ≤ D.moduleSubgroup from inf_le_right)) (inclusion_injective _)
  have hne : C ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hC
    exact hp.ne_one hC.symm
  have hfix : Z ⊓ centralizer (C : Set G) = ⊥ := by
    apply bot_unique
    exact (inf_le_inf_right _ (show Z ≤ D.moduleSubgroup from inf_le_right)).trans_eq
      (natural_cartan_subgroup_fixed_eq_bot c hnat C hCA hne)
  exact primitive_prime_invariant_eq_bot_or_self Z C hp hp2 hC hord
    (fundamental_point_card D hTL hpsl hodd hnat) hfix X hXZ hCX

/-- Any point-stabilizing overgroup of the primitive Cartan subgroup acts
irreducibly; hence its full ambient normalizer has the required point TI. -/
theorem fundamental_point_ti_under_primitive_actor_normalizer
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hodd : Odd n)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (c : CartanPair T L H A B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : orderOf (2 : ZMod p) = n)
    (C P : Subgroup G) (hCA : C ≤ A) (hC : Nat.card C = p)
    (hCP : C ≤ P) (hPZ : P ≤ (setup T L D.moduleSubgroup H A).G₁)
    {g : G} (hg : g ∈ normalizer (P : Set G)) :
    let Z := (setup T L D.moduleSubgroup H A).V₁
    Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨ Z.map (MulAut.conj g).toMonoidHom = Z := by
  apply ti_under_actor_normalizer _ P hPZ _ hg
  intro X hXZ hPX
  exact fundamental_point_primitive_irreducible D hTL hpsl hodd hnat c hp hp2 hord C hCA hC
    X hXZ (hCP.trans hPX)

/-- Zsigmondy constructs the actual Cartan actor, and its full ambient normalizer is TI. -/
theorem fundamental_primitive_actor_exists
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hn : 1 < n) (hodd : Odd n) (hnat : IsNaturalModule L D.moduleSubgroup n)
    (c : CartanPair T L H A B) :
    ∃ (p : ℕ) (C : Subgroup G), p.Prime ∧ p ≠ 2 ∧
      orderOf (2 : ZMod p) = n ∧ C ≤ A ∧ Nat.card C = p ∧
      (∀ X : Subgroup G, X ≤ (setup T L D.moduleSubgroup H A).V₁ →
        C ≤ normalizer (X : Set G) → X = ⊥ ∨ X = (setup T L D.moduleSubgroup H A).V₁) ∧
      ∀ g ∈ normalizer (C : Set G),
        (setup T L D.moduleSubgroup H A).V₁ ⊓
            (setup T L D.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
          (setup T L D.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom =
            (setup T L D.moduleSubgroup H A).V₁ := by
  obtain ⟨p,C,hp,hp2,ho,hCA,hC⟩ := cartan_primitive_prime_subgroup c hTL hpsl hn hodd
  have hCZ : C ≤ (setup T L D.moduleSubgroup H A).G₁ :=
    ((hCA.trans c.left_le).trans (fundamental_point_normalizer D hTL hpsl hodd hnat).ge).trans inf_le_right
  exact ⟨p,C,hp,hp2,ho,hCA,hC,
    fundamental_point_primitive_irreducible D hTL hpsl hodd hnat c hp hp2 ho C hCA hC,
    fun _ hg => fundamental_point_ti_under_primitive_actor_normalizer D hTL hpsl hodd hnat c
      hp hp2 ho C C hCA hC le_rfl hCZ hg⟩

/-- Choose a Sylow subgroup of the point stabilizer in the literal quotient-centralizer,
containing the primitive Cartan actor. Its full normalizer already has point TI. -/
theorem fundamental_point_stabilizer_sylow_exists
    {W : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hodd : Odd n) (hnat : IsNaturalModule L D.moduleSubgroup n)
    (c : CartanPair T L H A B) :
    let J := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
      (normalizer (residual H : Set G)).subtype ⊓ (setup T L D.moduleSubgroup H A).G₁
    ∃ (p : ℕ) (_hp : Fact p.Prime) (C : Subgroup G) (P : Sylow p J),
      p ≠ 2 ∧ orderOf (2 : ZMod p) = n ∧ C ≤ A ∧ Nat.card C = p ∧
      C ≤ (P : Subgroup J).map J.subtype ∧
      ∀ g ∈ normalizer ((P : Subgroup J).map J.subtype : Set G),
        (setup T L D.moduleSubgroup H A).V₁ ⊓
            (setup T L D.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
          (setup T L D.moduleSubgroup H A).V₁.map (MulAut.conj g).toMonoidHom =
            (setup T L D.moduleSubgroup H A).V₁ := by
  let J := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
    (normalizer (residual H : Set G)).subtype ⊓ (setup T L D.moduleSubgroup H A).G₁
  obtain ⟨p,C,hp,hp2,ho,hCA,hC⟩ := cartan_primitive_prime_subgroup c h.sylow_normalizes h.linear h.exponent hodd
  let hp' : Fact p.Prime := ⟨hp⟩
  have hCJ : C ≤ J := le_inf
    (hCA.trans (cartan_residual_action_trivial_of_odd h hH c hodd hK hnf hm))
    (hCA.trans (le_sup_right.trans (fundamental_join_le_point_normalizer h hH c hodd hK hnf D hnat)))
  have hc : IsPGroup p C := IsPGroup.of_card (n := 1) (by simpa using hC)
  obtain ⟨P,hP⟩ := (hc.comap_subtype (K := J)).exists_le_sylow
  have hP' : C.subgroupOf J ≤ (P : Subgroup J) := hP
  have hCP : C ≤ (P : Subgroup J).map J.subtype := by
    simpa only [map_subgroupOf_eq_of_le hCJ] using map_mono (f := J.subtype) hP'
  refine ⟨p,hp',C,P,hp2,ho,hCA,hC,hCP,?_⟩
  intro g hg
  exact fundamental_point_ti_under_primitive_actor_normalizer D h.sylow_normalizes h.linear hodd hnat c
    hp hp2 ho C ((P : Subgroup J).map J.subtype) hCA hC hCP
    ((map_subtype_le _).trans inf_le_right) hg

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
