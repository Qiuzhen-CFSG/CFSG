module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Transport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Interchange

/-!
# Choosing the two noncommuting cover seeds

Generation U_H = ⟨V₃^H⟩ supplies two actual H-conjugates with nontrivial
commutator. In the left-conjugation convention the new return element is
k⁻¹ g h. Right multiplication by h fixes U_H, O₂(H), H and its central line;
left multiplication by k⁻¹ conjugates the transported configuration. Every
kernel, center and endpoint condition is retained explicitly.

The transported kernel centralizes U_H, so the chosen seed has nontrivial
image in the literal H/O₂(H). Its nontrivial commutator is the order-two
transported central line. Relative abelianness then gives the centralizer
and normalizer containments, and the conjugate of precisely 13.5.5 gives
placement in M_V^g.

Source: Aschbacher–Smith 13.8.7, printed p.949; the explicit inputs are the
transported F.9 configuration, 13.7.2 and 13.5.5. No seed is an input.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverGeometry
variable {G : Type*} [Group G]

private theorem conj_commutator (X Y : Subgroup G) (g : G) :
    (⁅X, Y⁆).conjBy g = ⁅X.conjBy g, Y.conjBy g⁆ := map_commutator _ _ _

private theorem conj_le_conj_iff (X Y : Subgroup G) (g : G) :
    X.conjBy g ≤ Y.conjBy g ↔ X ≤ Y := by
  constructor
  · intro h
    have hi := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
    change (X.conjBy g).conjBy g⁻¹ ≤ (Y.conjBy g).conjBy g⁻¹ at hi
    simpa only [conjBy_inv] using hi
  · exact map_mono

private theorem conj_ne_bot {X : Subgroup G} (g : G) (h : X ≠ ⊥) :
    X.conjBy g ≠ ⊥ := by
  intro he
  apply h
  have hh := congrArg (fun S : Subgroup G => S.conjBy g⁻¹) he
  rw [conjBy_inv] at hh
  simpa only [conjBy, Subgroup.map_bot] using hh

/-- Noncommutation with a generated conjugate span is witnessed on an actual seed. -/
theorem exists_noncommuting_conjugate (H C X : Subgroup G) (g : G)
    (hn : ⁅(Source.UH H C).conjBy g, X⁆ ≠ ⊥) :
    ∃ h ∈ H, ⁅C.conjBy (g * h), X⁆ ≠ ⊥ := by
  by_contra! hh
  apply hn
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply (map_le_iff_le_comap).mpr
  apply (closure_le _).mpr
  rintro x ⟨h, hhH, c, hc, rfl⟩
  have hle := commutator_eq_bot_iff_le_centralizer.mp (hh h hhH)
  apply hle
  rw [conjBy_mul]
  exact mem_map_of_mem _ (mem_map_of_mem _ hc)

/-- Both H-adjustments are explicit. In the left-conjugation convention the
new return element is k⁻¹ g h. -/
theorem exists_double_adjustment (H C : Subgroup G) (g : G)
    (hn : ⁅(Source.UH H C).conjBy g, Source.UH H C⁆ ≠ ⊥) :
    ∃ h ∈ H, ∃ k ∈ H, ⁅C.conjBy (k⁻¹ * (g * h)), C⁆ ≠ ⊥ := by
  obtain ⟨h, hh, hn⟩ := exists_noncommuting_conjugate H C (Source.UH H C) g hn
  have hn' : ⁅(Source.UH H C).conjBy 1, C.conjBy (g * h)⁆ ≠ ⊥ := by
    rwa [conjBy_one, commutator_comm]
  obtain ⟨k, hk, hnk⟩ := exists_noncommuting_conjugate H C (C.conjBy (g * h)) 1 hn'
  rw [one_mul] at hnk
  have hd := conj_ne_bot k⁻¹ hnk
  rw [conj_commutator, conjBy_inv, conjBy_conjBy, commutator_comm] at hd
  exact ⟨h, hh, k, hk, hd⟩

/-- H fixes its central cyclic line, not merely its set of involutions. -/
theorem fixes_central_line (H : Subgroup G) (z h : G)
    (hH : H = centralizer ({z} : Set G)) (hh : h ∈ H) :
    (zpowers z).conjBy h = zpowers z := by
  have hc : h * z = z * h := mem_centralizer_singleton_iff.mp (hH ▸ hh)
  change (zpowers z).map _ = _
  rw [MonoidHom.map_zpowers]
  congr 1
  change h * z * h⁻¹ = z
  rw [hc, mul_inv_cancel_right]

/-- Every subgroup normalized by H transforms predictably under both adjustments. -/
theorem double_adjustment_conjugate (H X : Subgroup G) (g h k : G)
    (hn : H ≤ normalizer X) (hh : h ∈ H) :
    X.conjBy (k⁻¹ * (g * h)) = (X.conjBy g).conjBy k⁻¹ := by
  have he : X.conjBy h = X := mem_normalizer_iff_map_conj_eq.mp (hn hh)
  rw [conjBy_mul, conjBy_mul, he]

/-- The adjusted element stays in every permitted overgroup containing H and g. -/
theorem adjusted_mem (H J : Subgroup G) (g h k : G)
    (hHJ : H ≤ J) (hg : g ∈ J) (hh : h ∈ H) (hk : k ∈ H) :
    k⁻¹ * (g * h) ∈ J :=
  J.mul_mem (J.inv_mem (hHJ hk)) (J.mul_mem hg (hHJ hh))

/-- The conjugate endpoint is exactly the normalizer of its actual center line. -/
theorem center_normalizer_eq_conjugate_H (H : Subgroup G) (z g : G)
    (hH : H = centralizer ({z} : Set G))
    (hcard : Nat.card (zpowers z) = 2) :
    normalizer ((zpowers z).conjBy g) = H.conjBy g := by
  have hz : z ≠ 1 := by
    intro hz
    subst z
    have hh : Nat.card (zpowers (1 : G)) = 1 := by simp
    omega
  have hn : normalizer (zpowers z) = H := by
    apply le_antisymm
    · rw [hH]
      exact normalizer_line_le_centralizer z hz hcard
    · intro h hh
      exact mem_normalizer_iff_map_conj_eq.mpr (fixes_central_line H z h hH hh)
  change normalizer (((zpowers z).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) = _
  rw [← map_equiv_normalizer_eq, hn]
  rfl

/-- All conditions of the transported pair survive both seed adjustments.
The hypotheses are the transported F.9 conclusions, with relative H-normality. -/
theorem adjusted_configuration (H C Z Q : Subgroup G) (g h k : G)
    (hU : H ≤ normalizer (Source.UH H C))
    (hZ : H ≤ normalizer Z) (hQ : H ≤ normalizer Q)
    (hh : h ∈ H) (hk : k ∈ H)
    (hc : ⁅Source.UH H C, (Source.UH H C).conjBy g⁆ = Z.conjBy g)
    (hin : Source.UH H C ≤ Q.conjBy g)
    (hout : ¬ (Source.UH H C).conjBy g ≤ Q)
    (hdis : Z.conjBy g ⊓ Z = ⊥)
    (hPH : (Source.UH H C).conjBy g ≤ H)
    (hker : ⁅(Source.UH H C).conjBy g ⊓ Q, Source.UH H C⁆ = ⊥) :
    let g' := k⁻¹ * (g * h)
    ⁅Source.UH H C, (Source.UH H C).conjBy g'⁆ = Z.conjBy g' ∧
    Source.UH H C ≤ Q.conjBy g' ∧
    ¬ (Source.UH H C).conjBy g' ≤ Q ∧
    Z.conjBy g' ⊓ Z = ⊥ ∧
    (Source.UH H C).conjBy g' ≤ H ∧
    ⁅(Source.UH H C).conjBy g' ⊓ Q, Source.UH H C⁆ = ⊥ ∧
    H.conjBy g' = (H.conjBy g).conjBy k⁻¹ := by
  dsimp only
  have hUi : (Source.UH H C).conjBy k⁻¹ = Source.UH H C :=
    mem_normalizer_iff_map_conj_eq.mp (hU (H.inv_mem hk))
  have hZi : Z.conjBy k⁻¹ = Z :=
    mem_normalizer_iff_map_conj_eq.mp (hZ (H.inv_mem hk))
  have hQi : Q.conjBy k⁻¹ = Q :=
    mem_normalizer_iff_map_conj_eq.mp (hQ (H.inv_mem hk))
  have hHi : H.conjBy k⁻¹ = H :=
    mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer (H.inv_mem hk))
  rw [double_adjustment_conjugate H _ g h k hU hh,
    double_adjustment_conjugate H _ g h k hZ hh,
    double_adjustment_conjugate H _ g h k hQ hh,
    double_adjustment_conjugate H _ g h k H.le_normalizer hh]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · have hi := congrArg (fun S : Subgroup G => S.conjBy k⁻¹) hc
    rwa [conj_commutator, hUi] at hi
  · have hi := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hin
    change (Source.UH H C).conjBy k⁻¹ ≤ (Q.conjBy g).conjBy k⁻¹ at hi
    rwa [hUi] at hi
  · intro hi
    apply hout
    apply (conj_le_conj_iff _ _ k⁻¹).mp
    rwa [hQi]
  · have hi := congrArg (fun S : Subgroup G => S.conjBy k⁻¹) hdis
    change (Z.conjBy g ⊓ Z).map _ = (⊥ : Subgroup G).map _ at hi
    rw [map_inf _ _ _ (MulAut.conj k⁻¹).injective, Subgroup.map_bot] at hi
    change (Z.conjBy g).conjBy k⁻¹ ⊓ Z.conjBy k⁻¹ = ⊥ at hi
    rwa [hZi] at hi
  · have hi := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hPH
    change ((Source.UH H C).conjBy g).conjBy k⁻¹ ≤ H.conjBy k⁻¹ at hi
    rwa [hHi] at hi
  · have hi := congrArg (fun S : Subgroup G => S.conjBy k⁻¹) hker
    rw [conj_commutator, hUi] at hi
    change ⁅((Source.UH H C).conjBy g ⊓ Q).map _, Source.UH H C⁆ =
      (⊥ : Subgroup G).map _ at hi
    rw [map_inf _ _ _ (MulAut.conj k⁻¹).injective, Subgroup.map_bot] at hi
    change ⁅((Source.UH H C).conjBy g).conjBy k⁻¹ ⊓ Q.conjBy k⁻¹, Source.UH H C⁆ = ⊥ at hi
    rwa [hQi] at hi

/-- The literal transported F.9 configuration; no seed choice or geometric
conclusion is included. -/
structure Configuration (H C Z Q : Subgroup G) (g : G) : Prop where
  commutator_eq : ⁅Source.UH H C, (Source.UH H C).conjBy g⁆ = Z.conjBy g
  inside : Source.UH H C ≤ Q.conjBy g
  outside : ¬ (Source.UH H C).conjBy g ≤ Q
  disjoint : Z.conjBy g ⊓ Z = ⊥
  in_H : (Source.UH H C).conjBy g ≤ H
  kernel_centralizes : ⁅(Source.UH H C).conjBy g ⊓ Q, Source.UH H C⁆ = ⊥

/-- Assemble the input directly from the genuine critical-pair transport.
The extra premises are exactly the earlier F.9 kernel, disjointness and
cross-centralization conclusions recorded in Transport.lean. -/
theorem Configuration.of_criticalPair [Finite G]
    {L T H V : Subgroup G} (c : CriticalPair L T H V) (C Z : Subgroup G)
    (hcard : Nat.card Z = 2)
    (hn : c.Ugamma C ≤ normalizer (Z : Set G))
    (hstrict : Source.DH (Source.UH H C) (c.Ugamma C) (c.Aone Z) < Source.UH H C)
    (hfull : Source.Dgamma (c.Ugamma C) (Source.UH H C) Z = c.Ugamma C)
    (hDH : Source.DH (Source.UH H C) (c.Ugamma C) (c.Aone Z) =
      Source.UH H C ⊓ c.Qgamma)
    (hDγ : Source.Dgamma (c.Ugamma C) (Source.UH H C) Z = c.Ugamma C ⊓ Source.QH H)
    (hdisj : Z ⊓ c.Aone Z = ⊥)
    (hUend : Source.UH H C ≤ vertexGroup L T H c.gamma)
    (hcross : ⁅Source.DH (Source.UH H C) (c.Ugamma C) (c.Aone Z),
      Source.Dgamma (c.Ugamma C) (Source.UH H C) Z⁆ = ⊥) :
    Configuration H C Z (Source.QH H) (returnElement c : G) := by
  obtain ⟨hc, hi, ho, hd⟩ := transported_configuration c C Z hcard hn
    hstrict hfull hDH hDγ hdisj
  exact ⟨hc, hi, ho, hd, return_conjugate_le_H c _ hUend,
    transported_denominator_centralizes c C Z hfull hDH hcross⟩

/-- The star image here is the actual H/O₂(H) image. -/
theorem starImage_ne_bot_of_not_le (H B : Subgroup G) (hBH : B ≤ H)
    (hBQ : ¬ B ≤ Source.QH H) : Source.starImage H B ≠ ⊥ := by
  intro he
  have hb : B.subgroupOf H ≤ pCore 2 H := by
    rw [← QuotientGroup.ker_mk' (pCore 2 H)]
    have hi := (map_le_iff_le_comap).mp he.le
    exact hi
  apply hBQ
  intro b hbB
  exact mem_map_of_mem H.subtype (hb (show (⟨b, hBH hbB⟩ : H) ∈ B.subgroupOf H from hbB))

/-- Transport the precise 13.5.5 normalizer intersection. -/
theorem normalizer_intersection_conjugate (Z C M : Subgroup G) (g : G)
    (h : normalizer Z ⊓ normalizer C ≤ M) :
    normalizer (Z.conjBy g) ⊓ normalizer (C.conjBy g) ≤ M.conjBy g := by
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) h
  rw [map_inf _ _ _ (MulAut.conj g).injective,
    map_equiv_normalizer_eq, map_equiv_normalizer_eq] at hh
  exact hh

/-- The genuine two-sided choice, with every transported condition preserved.
Nontrivial star image follows from the kernel centralization, so it is not
an independent seed hypothesis. The final containment uses exactly 13.5.5. -/
theorem choose_seed [Finite G]
    (H C M : Subgroup G) (z g : G)
    (hH : H = centralizer ({z} : Set G))
    (hcard : Nat.card (zpowers z) = 2) (hZC : zpowers z ≤ C)
    (habel : ⁅Source.UH H C, Source.UH H C⁆ = ⊥)
    (hM : normalizer (zpowers z) ⊓ normalizer C ≤ M)
    (cfg : Configuration H C (zpowers z) (Source.QH H) g) :
    ∃ h ∈ H, ∃ k ∈ H,
      let g' := k⁻¹ * (g * h)
      let B := C.conjBy g'
      let A := (zpowers z).conjBy g'
      Configuration H C (zpowers z) (Source.QH H) g' ∧
      H.conjBy g' = (H.conjBy g).conjBy k⁻¹ ∧
      (Source.UH H C).conjBy g' = ((Source.UH H C).conjBy g).conjBy k⁻¹ ∧
      A = ((zpowers z).conjBy g).conjBy k⁻¹ ∧
      B ≤ H ∧ Source.starImage H B ≠ ⊥ ∧
      ⁅B, C⁆ ≠ ⊥ ∧ ⁅B, C⁆ = A ∧ A ≤ B ∧
      C ≤ centralizer A ⊓ normalizer B ∧
      centralizer A ⊓ normalizer B ≤ M.conjBy g' := by
  have hU := le_normalizer_conjugateSpanBy C H
  have hQ : H ≤ normalizer (Source.QH H) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hZ : H ≤ normalizer (zpowers z) := by
    intro h hh
    exact mem_normalizer_iff_map_conj_eq.mpr (fixes_central_line H z h hH hh)
  have hn : ⁅(Source.UH H C).conjBy g, Source.UH H C⁆ ≠ ⊥ := by
    rw [commutator_comm, cfg.commutator_eq]
    apply conj_ne_bot
    intro he
    have hec := card_eq_one.mpr he
    omega
  obtain ⟨h, hh, k, hk, hseed⟩ := exists_double_adjustment H C g hn
  obtain ⟨hc, hi, ho, hd, hp, hker, heH⟩ := adjusted_configuration
    H C (zpowers z) (Source.QH H) g h k hU hZ hQ hh hk
    cfg.commutator_eq cfg.inside cfg.outside cfg.disjoint cfg.in_H cfg.kernel_centralizes
  let g' := k⁻¹ * (g * h)
  let A := (zpowers z).conjBy g'
  let B := C.conjBy g'
  have hCU : C ≤ Source.UH H C := le_conjugateSpanBy C H
  have hBP : B ≤ (Source.UH H C).conjBy g' := map_mono hCU
  have hBH : B ≤ H := hBP.trans hp
  have hAB : A ≤ B := map_mono hZC
  change ⁅Source.UH H C, (Source.UH H C).conjBy g'⁆ = A at hc
  have hcle : ⁅B, C⁆ ≤ A := by
    rw [← hc, commutator_comm B C]
    exact commutator_mono hCU hBP
  have hAsize : Nat.card A = 2 := by
    change Nat.card ((zpowers z).map _) = 2
    rw [card_map_of_injective (MulAut.conj g').injective, hcard]
  have hceq : ⁅B, C⁆ = A := by
    have hdiv : Nat.card (⁅B, C⁆ : Subgroup G) ∣ 2 := hAsize ▸ card_dvd_of_le hcle
    have hsz := ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (fun hh => hseed (card_eq_one.mp hh))
    exact eq_of_le_of_card_ge hcle (by rw [hAsize, hsz])
  have hstar : Source.starImage H B ≠ ⊥ := by
    apply starImage_ne_bot_of_not_le H B hBH
    intro hBQ
    apply hseed
    exact le_bot_iff.mp ((commutator_mono (le_inf hBP hBQ) hCU).trans hker.le)
  have hAU : A ≤ Source.UH H C := by
    rw [← hc]
    exact le_normalizer_iff_commutator_le_left.mp (hp.trans hU)
  have hcent : C ≤ centralizer A :=
    commutator_eq_bot_iff_le_centralizer.mp
      (le_bot_iff.mp ((commutator_mono hCU hAU).trans habel.le))
  have hnorm : C ≤ normalizer B :=
    le_normalizer_iff_commutator_le_left.mpr (hceq ▸ hAB)
  refine ⟨h, hh, k, hk, ⟨hc, hi, ho, hd, hp, hker⟩, heH,
    double_adjustment_conjugate H _ g h k hU hh,
    double_adjustment_conjugate H _ g h k hZ hh,
    hBH, hstar, hseed, hceq, hAB, le_inf hcent hnorm, ?_⟩
  intro x hx
  apply normalizer_intersection_conjugate (zpowers z) C M g' hM
  exact ⟨centralizer_le_normalizer (A : Set G) hx.1, hx.2⟩

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverGeometry
end
