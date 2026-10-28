module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.Torus.PrimeCore
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.Torus.Cyclic

/-!
# The torus witnesses force the literal odd residual to be noncyclic

Let W=⟨u,v⟩ be the original elementary four-subgroup of the two-point
stabilizer D, and adjoin its commuting involution t. The two marked square-field
tori supply nontrivial p-cores with opposite fixed/inverted actions. The same
W⟨t⟩-invariant Sylow subgroup of O₂′(D) admits equivariant embeddings of both
cores, because its conjugating elements centralize the entire actor group.
Their images lie in the literal Ru=[C_R₁(u),t] and Rv=[C_R₁(v),t].

The images give nontrivial opposite actions on Ru and Rv. They also exclude
cyclicity of R=[R₁,t]: one image is fixed by u and the other inverted, so they
are disjoint nontrivial p-subgroups. Such subgroups cannot lie in a cyclic
p-group. When the earlier circle models give cyclicity of Ru and Rv, their
involutory opposite actions are inversion on all of those literal subgroups.

The tori remain explicit genuine preceding model inputs, normally D∩Fu and
D∩Fv. Neither a p-core witness, nontrivial residual action nor noncyclicity is
assumed. Source: GLS IV, Chapter 2, Proposition 16.5,
refs/KGroup/GLS4/Chapter2.tex, lines 2935–2952.
-/

noncomputable section
namespace BenderSuzuki.ZD.NativeSource16
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem normalizes_of_conjugates_mem (T : Subgroup G) (a : G)
    (h : ∀ x ∈ T, a * x * a⁻¹ ∈ T) : a ∈ normalizer (T : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [card_map_of_injective (MulAut.conj a).injective]

/-- The two involution generators and t preserve the actual torus, so no
separate invariance premise on its p-core is required. -/
public theorem torus_fourActor_normalizes
    (W T : Subgroup G) (t u v : G) {m : ℕ}
    (hWgen : W = zpowers u ⊔ zpowers v)
    (hTu : T ≤ centralizer ({u} : Set G))
    (hTv : ∀ x ∈ T, v * x * v⁻¹ = x ^ (2 ^ m))
    (hTt : ∀ x ∈ T, t * x * t⁻¹ = x⁻¹) :
    W ⊔ zpowers t ≤ normalizer (T : Set G) := by
  rw [hWgen]
  refine sup_le (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)) (zpowers_le.mpr ?_)
  · apply Subgroup.centralizer_le_normalizer
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hTu hx)
  · exact normalizes_of_conjugates_mem T v (fun x hx => hTv x hx ▸ T.pow_mem hx _)
  · exact normalizes_of_conjugates_mem T t (fun x hx => hTt x hx ▸ T.inv_mem hx)

omit [Finite G] in
private theorem conjugate_ne_bot (Q : Subgroup G) (c : G) (hQ : Q ≠ ⊥) :
    Q.map (MulAut.conj c).toMonoidHom ≠ ⊥ := by
  intro he
  apply hQ
  apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
  simpa only [Subgroup.map_bot] using he

omit [Finite G] in
private theorem conjugate_le_centralizer (Q : Subgroup G) (c a : G)
    (hca : c * a = a * c) (hQ : Q ≤ centralizer ({a} : Set G)) :
    Q.map (MulAut.conj c).toMonoidHom ≤ centralizer ({a} : Set G) := by
  have hfix : MulAut.conj c a = a := by
    change c * a * c⁻¹ = a
    rw [hca, mul_inv_cancel_right]
  rintro _ ⟨x, hx, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have he := congrArg (MulAut.conj c) (mem_centralizer_singleton_iff.mp (hQ hx))
  change (MulAut.conj c) x * a = a * (MulAut.conj c) x
  simpa only [map_mul, hfix] using he

omit [Finite G] in
private theorem conjugate_inverted (Q : Subgroup G) (c a : G)
    (hca : c * a = a * c) (hQ : ∀ x ∈ Q, a * x * a⁻¹ = x⁻¹) :
    ∀ x ∈ Q.map (MulAut.conj c).toMonoidHom, a * x * a⁻¹ = x⁻¹ := by
  have hfix : MulAut.conj c a = a := by
    change c * a * c⁻¹ = a
    rw [hca, mul_inv_cancel_right]
  rintro _ ⟨x, hx, rfl⟩
  have he := congrArg (MulAut.conj c) (hQ x hx)
  change a * (MulAut.conj c) x * a⁻¹ = ((MulAut.conj c) x)⁻¹
  simpa only [map_mul, map_inv, hfix] using he

private theorem not_central_of_nontrivial_inverted
    (Q : Subgroup G) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hQp : IsPGroup p Q) (hQn : Q ≠ ⊥) (a : G)
    (hinv : ∀ x ∈ Q, a * x * a⁻¹ = x⁻¹) : ¬ Q ≤ centralizer ({a} : Set G) := by
  intro hQC
  apply hQn
  apply eq_bot_iff.mpr
  intro x hx
  have hc : x * a = a * x := mem_centralizer_singleton_iff.mp (hQC hx)
  have he : x = x⁻¹ := by
    calc
      x = a * x * a⁻¹ := by rw [← hc]; simp
      _ = x⁻¹ := hinv x hx
  have hs : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two _
      _ = x * x⁻¹ := congrArg (fun y => x * y) he
      _ = 1 := mul_inv_cancel _
  have hodd : Odd (Nat.card Q) := by
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    rw [hk]
    exact hp.pow
  have hx1 : (⟨x, hx⟩ : Q) = 1 := hodd.coprime_two_right.pow_left_bijective.injective (by
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, one_pow] using hs)
  exact congrArg Subtype.val hx1

/-- The two actual marked tori force the original residual R to be noncyclic.
The same chosen invariant Sylow contains equivariant images of both torus
p-cores. Nontrivial opposite actions on the literal Ru and Rv are constructed;
when model containment gives their cyclicity, those actions are inversion. -/
public theorem residualFourActor_noncyclic_of_torus_actions
    {Z : Set G} {M : Subgroup G} {t : G}
    (h : IsProductDisconnected Z M) (ht : t ∈ Z) (htM : t ∉ M)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWD : W ≤ residualPairStabilizer M t) (hWt : W ≤ centralizer ({t} : Set G))
    (u v : G) (hu : u ∈ W) (hv : v ∈ W)
    (hWgen : W = zpowers u ⊔ zpowers v)
    (Tu Tv : Subgroup G) {m p : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hpdiv : p ∣ 2 ^ m + 1)
    (hTuc : IsCyclic Tu) (hTvc : IsCyclic Tv)
    (hTuo : Nat.card Tu = 2 ^ (2 * m) - 1) (hTvo : Nat.card Tv = 2 ^ (2 * m) - 1)
    (hTuD : Tu ≤ residualPairStabilizer M t) (hTvD : Tv ≤ residualPairStabilizer M t)
    (hTuu : Tu ≤ centralizer ({u} : Set G)) (hTvv : Tv ≤ centralizer ({v} : Set G))
    (hTuv : ∀ x ∈ Tu, v * x * v⁻¹ = x ^ (2 ^ m))
    (hTvu : ∀ x ∈ Tv, u * x * u⁻¹ = x ^ (2 ^ m))
    (hTut : ∀ x ∈ Tu, t * x * t⁻¹ = x⁻¹)
    (hTvt : ∀ x ∈ Tv, t * x * t⁻¹ = x⁻¹) :
    let A := W ⊔ zpowers t
    let : Fact p.Prime := ⟨hp⟩
    Nat.card A = 8 ∧ ∃ P : Sylow p (residualOddCore M t),
      let P₁ := (P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype
      ∃ _hAP : A ≤ normalizer P₁,
        let R := OddInvolutionFrattini.R P₁ t
        let Ru := OddInvolutionFrattini.Rw P₁ t u
        let Rv := OddInvolutionFrattini.Rw P₁ t v
        ¬ IsCyclic R ∧
          (¬ Ru ≤ centralizer ({v} : Set G)) ∧
          (¬ Rv ≤ centralizer ({u} : Set G)) ∧
          (IsCyclic Ru → ∀ x ∈ Ru, v * x * v⁻¹ = x⁻¹) ∧
          (IsCyclic Rv → ∀ x ∈ Rv, u * x * u⁻¹ = x⁻¹) := by
  let A := W ⊔ zpowers t
  let : Fact p.Prime := ⟨hp⟩
  let := residualFourActor_elementary (h.involutions t ht) W hWt
  have hpo : Odd p := prime_dividing_binary_succ_odd hm hp hpdiv
  have huA : u ∈ A := mem_sup_left hu
  have hvA : v ∈ A := mem_sup_left hv
  have htA : t ∈ A := mem_sup_right (mem_zpowers t)
  have hATu := torus_fourActor_normalizes W Tu t u v hWgen hTuu hTuv hTut
  have hATv := torus_fourActor_normalizes W Tv t v u
    (hWgen.trans (sup_comm _ _)) hTvv hTvu hTvt
  obtain ⟨hQun, hQup, hQuD, hAQu, hQuu, hQuv, hQut⟩ :=
    torus_pCore_profile (residualPairStabilizer M t) A Tu t u v hm hp hpdiv
      hTuc hTuo hTuD hATu hTuu hTuv hTut
  obtain ⟨hQvn, hQvp, hQvD, hAQv, hQvv, hQvu, hQvt⟩ :=
    torus_pCore_profile (residualPairStabilizer M t) A Tv t v u hm hp hpdiv
      hTvc hTvo hTvD hATv hTvv hTvu hTvt
  obtain ⟨hcard, P, hAP, hcontrol⟩ := residualFourActor_sylow_fixed_embedding
    h ht htM W hW hWD hWt p
  let P₁ := (P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype
  let R := OddInvolutionFrattini.R P₁ t
  let Ru := OddInvolutionFrattini.Rw P₁ t u
  let Rv := OddInvolutionFrattini.Rw P₁ t v
  obtain ⟨cu, hcu, hXu, _⟩ := hcontrol (Tu.pCoreIn p) hQuD hQup hAQu u huA hQuu hQut
  obtain ⟨cv, hcv, hYv, _⟩ := hcontrol (Tv.pCoreIn p) hQvD hQvp hAQv v hvA hQvv hQvt
  let X := (Tu.pCoreIn p).map (MulAut.conj (cu : G)).toMonoidHom
  let Y := (Tv.pCoreIn p).map (MulAut.conj (cv : G)).toMonoidHom
  have hXn : X ≠ ⊥ := conjugate_ne_bot _ _ hQun
  have hYn : Y ≠ ⊥ := conjugate_ne_bot _ _ hQvn
  have hXp : IsPGroup p X := hQup.map _
  have hYp : IsPGroup p Y := hQvp.map _
  have hXfix : X ≤ centralizer ({u} : Set G) :=
    conjugate_le_centralizer _ _ _ ((mem_centralizer_iff.mp hcu) u huA).symm hQuu
  have hXinv : ∀ x ∈ X, v * x * v⁻¹ = x⁻¹ :=
    conjugate_inverted _ _ _ ((mem_centralizer_iff.mp hcu) v hvA).symm hQuv
  have hYinv : ∀ x ∈ Y, u * x * u⁻¹ = x⁻¹ :=
    conjugate_inverted _ _ _ ((mem_centralizer_iff.mp hcv) u huA).symm hQvu
  have hRuopp : ¬ Ru ≤ centralizer ({v} : Set G) := fun he =>
    not_central_of_nontrivial_inverted X hpo hXp hXn v hXinv (hXu.trans he)
  have hRvopp : ¬ Rv ≤ centralizer ({u} : Set G) := fun he =>
    not_central_of_nontrivial_inverted Y hpo hYp hYn u hYinv (hYv.trans he)
  have hPp : IsPGroup p P₁ := P.isPGroup'.map _
  have hRP : R ≤ P₁ := OddInvolutionFrattini.r_le P₁ (hAP htA)
  have hRup : IsPGroup p Ru := hPp.of_injective
    (inclusion ((OddInvolutionFrattini.rw_le P₁ t u).trans hRP)) (inclusion_injective _)
  have hRvp : IsPGroup p Rv := hPp.of_injective
    (inclusion ((OddInvolutionFrattini.rw_le P₁ t v).trans hRP)) (inclusion_injective _)
  have ha2 (a : A) : (a : G) ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) a)
  refine ⟨hcard, P, hAP, noncyclic_of_fixed_inverted_pSubgroups R X Y hpo
    (hXu.trans (OddInvolutionFrattini.rw_le P₁ t u))
    (hYv.trans (OddInvolutionFrattini.rw_le P₁ t v)) hXp hYp hXn hYn u hXfix hYinv,
    hRuopp, hRvopp, ?_, ?_⟩
  · intro hcyc
    let : IsCyclic Ru := hcyc
    exact involution_inverts_cyclic_pSubgroup Ru hRup hpo v (ha2 ⟨v, hvA⟩)
      (OddInvolutionFrattini.normalizes_Rw P₁ A hAP htA huA hvA) hRuopp
  · intro hcyc
    let : IsCyclic Rv := hcyc
    exact involution_inverts_cyclic_pSubgroup Rv hRvp hpo u (ha2 ⟨u, huA⟩)
      (OddInvolutionFrattini.normalizes_Rw P₁ A hAP htA hvA huA) hRvopp

end BenderSuzuki.ZD.NativeSource16
