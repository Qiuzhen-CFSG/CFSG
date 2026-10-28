module

public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.FiveTwoPStarCentralizer
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Stellmacher.OmegaOneCenterMap

/-!
# Ambient residual subnormality at an embedded order-two vertex

In an ambient Section Nine context, an explicitly order-two vertex center
forces the common Sylow subgroup to equal the fixed ambient Sylow subgroup.
The image of its two-residual is subnormal in the full ambient centralizer
of the mapped center, and that centralizer has characteristic two type.
The graph group need only embed in the ambient group; its image need not be top.

Move the vertex to a distinguished coset. Its center contains the nontrivial
omega-center of the common Sylow subgroup, so cardinality two makes these
equal. Injectivity transports that equality and normality to the ambient
local subgroup. Alternatives (5.1)(a) and (c) are impossible. In (b), the left
orbit would make the omega-center normal in the join of the two local
subgroups, contradicting the join's trivial two-core. On the right orbit,
the P-star theorem gives ambient residual subnormality. The order-two
omega-center has equal normalizer and centralizer, and the latter contains
the fixed ambient Sylow subgroup. Hypothesis One therefore gives
characteristic two there. Finally, ambient conjugation transports the mapped
residual, full centralizer, subnormality and characteristic two to the chosen
vertex. Hypothesis One is applied before conjugation, never to a subgroup
merely containing an unspecified conjugate Sylow subgroup.

This supplies the ambient order-two input for the centralizer argument in
(9.1). Source: Stellmacher, Journal of Algebra 190 (1997), (5.1)(b), the
P-star definition and the opening reduction of (5.2); compare the order-two
vertex argument on printed p.54. The graph reductions follow
`SectionFiveToSeven/OrderTwoVertexResidual.lean`, with normality taken in the
generated join rather than in the full ambient group.
-/

open scoped Pointwise
namespace Stellmacher.SectionNine
open Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
variable {S P1 P2 : Subgroup H}
private theorem base_stabilizer (Γ : CosetGraphContext H S P1 P2)
    (coset : H → Γ.Vertex) (P : Subgroup H)
    (hact : ∀ g h, Γ.act g (coset h) = coset (h * g))
    (heq : ∀ g h, coset g = coset h ↔
      MulOpposite.op g • (P : Set H) = MulOpposite.op h • (P : Set H)) :
    Γ.stabilizer (coset 1) = P := by
  ext element
  have hmem : element ∈ Γ.stabilizer (coset 1) ↔
      Γ.act element (coset 1) = coset 1 :=
    Set.ext_iff.mp (Γ.stabilizer_def (coset 1)) element
  rw [hmem, hact, one_mul, heq]
  simp only [MulOpposite.op_one, one_smul]
  constructor
  · intro hsets
    change element ∈ (P : Set H)
    rw [← hsets]
    exact Set.mem_smul_set.mpr ⟨1, P.one_mem, by simp⟩
  · exact fun hmem ↦ op_smul_coe_set hmem

private theorem omega_ne_bot (S : Subgroup H)
    (hS : IsPGroup 2 S) (hne : S ≠ ⊥) : omegaOneCenter S ≠ ⊥ := by
  let _ : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hne
  let _ : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  obtain ⟨power, hpos, hcard⟩ :=
    (hS.to_subgroup (Subgroup.center S)).nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hpos)
  have hinner := omega₁_map_subtype_ne_bot (G := S) (Subgroup.center S) 2 hdvd
  intro hbot
  apply hinner
  apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
  simpa [omegaOneCenter] using hbot

private theorem base_center (Γ : CosetGraphContext H S P1 P2)
    (base : Γ.Vertex) (P : Subgroup H) (hbase : Γ.stabilizer base = P)
    (hsyl : IsSylowTwoIn S P) (hne : omegaOneCenter S ≠ ⊥)
    (hcard : Nat.card (Γ.z base) = 2) :
    Γ.z base = omegaOneCenter S ∧ NormalIn (omegaOneCenter S) P := by
  have hle : omegaOneCenter S ≤ Γ.z base := by
    obtain ⟨_, sylow, hsylow⟩ := hsyl
    change omegaOneCenter S ≤ Γ.zAt base
    rw [Γ.zAt_def]
    change omegaOneCenter S ≤ sSup {Z : Subgroup H |
      ∃ T : Sylow 2 (Γ.stabilizer base),
        Z = omegaOneCenter ((T : Subgroup (Γ.stabilizer base)).map
          (Γ.stabilizer base).subtype)}
    rw [hbase]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  have hequal : Γ.z base = omegaOneCenter S := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard]
    exact (Subgroup.one_lt_card_iff_ne_bot (omegaOneCenter S)).mpr hne
  refine ⟨hequal, (Subgroup.map_subtype_le _).trans hsyl.1, ?_⟩
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((Subgroup.map_subtype_le _).trans hsyl.1)).mpr
  change P ≤ Subgroup.normalizer (omegaOneCenter S : Set H)
  rw [← hbase, ← hequal]
  exact stabilizer_le_normalizer_z Γ base

omit [Finite H] in
private theorem subnormal_map (equiv : H ≃* H) (A P : Subgroup H)
    (hsub : SubnormalIn A P) :
    SubnormalIn (A.map equiv.toMonoidHom) (P.map equiv.toMonoidHom) := by
  let restricted : P ≃* P.map equiv.toMonoidHom :=
    P.equivMapOfInjective equiv.toMonoidHom equiv.injective
  have hmapped : ((A.subgroupOf P).map restricted.toMonoidHom).IsSubnormal :=
    hsub.2.map restricted.surjective
  refine ⟨Subgroup.map_mono hsub.1, ?_⟩
  have heq : (A.subgroupOf P).map restricted.toMonoidHom =
      (A.map equiv.toMonoidHom).subgroupOf (P.map equiv.toMonoidHom) := by
    apply Subgroup.map_injective (P.map equiv.toMonoidHom).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_mono hsub.1)]
    have hcomp : (P.map equiv.toMonoidHom).subtype.comp restricted.toMonoidHom =
        equiv.toMonoidHom.comp P.subtype := rfl
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hsub.1]
  rwa [← heq]

omit [Finite H] in
private theorem centralizer_map (A : Subgroup H) (equiv : H ≃* H) :
    (Subgroup.centralizer (A : Set H)).map equiv.toMonoidHom =
      Subgroup.centralizer (A.map equiv.toMonoidHom : Set H) := by
  ext element
  constructor
  · rintro ⟨preimage, hpreimage, rfl⟩
    change preimage ∈ Subgroup.centralizer (A : Set H) at hpreimage
    change equiv preimage ∈ Subgroup.centralizer (A.map equiv.toMonoidHom : Set H)
    rw [Subgroup.mem_centralizer_iff] at hpreimage ⊢
    rintro _ ⟨member, hmember, rfl⟩
    simpa using congrArg equiv (hpreimage member hmember)
  · intro hmem
    refine ⟨equiv.symm element, ?_, by simp⟩
    change equiv.symm element ∈ Subgroup.centralizer (A : Set H)
    rw [Subgroup.mem_centralizer_iff] at hmem ⊢
    intro member hmember
    apply equiv.injective
    simpa using hmem (equiv member) ⟨member, hmember, rfl⟩

private theorem characteristicTwo_map_equiv
    {G : Type u} [Group G]
    (e : G ≃* G) (P : Subgroup G)
    (hchar : Stellmacher.IsCharacteristicTwoType P) :
    Stellmacher.IsCharacteristicTwoType (P.map e.toMonoidHom) := by
  let eP : P ≃* P.map e.toMonoidHom :=
    P.equivMapOfInjective e.toMonoidHom e.injective
  have hcore : (pCore 2 P).map eP.toMonoidHom =
      pCore 2 (P.map e.toMonoidHom) :=
    pCore_map_iso 2 eP
  intro y hy
  let x : P := eP.symm y
  have hxcentral : x ∈ Subgroup.centralizer (pCore 2 P : Set P) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply eP.injective
    have heq := Subgroup.mem_centralizer_iff.mp hy (eP q)
      (hcore ▸ Subgroup.mem_map_of_mem eP.toMonoidHom hq)
    change eP (q * x) = eP (x * q)
    rw [map_mul, map_mul, show eP x = y from eP.apply_symm_apply y]
    exact heq
  have hxcore := hchar hxcentral
  have heycore : eP x ∈ pCore 2 (P.map e.toMonoidHom) := by
    rw [← hcore]
    exact Subgroup.mem_map_of_mem eP.toMonoidHom hxcore
  simpa only [x, eP.apply_symm_apply] using heycore

private theorem base_image
    {S0 : Sylow 2 H} {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (base : ctx.Γ.Vertex) (P : Subgroup G) (Q : Subgroup H)
    (hbase : ctx.Γ.stabilizer base = P) (hsyl : IsSylowTwoIn T P)
    (hmap : P.map embedding = Q) (hcard : Nat.card (ctx.Γ.z base) = 2) :
    (ctx.Γ.z base).map embedding = omegaOneCenter S ∧
      NormalIn (omegaOneCenter S) Q ∧ Nat.card (omegaOneCenter S) = 2 := by
  have hTp : IsPGroup 2 T := by
    have hp := ctx.hypothesisTwo.fiveOne.S_le_S0
    have hm : IsPGroup 2 (T.map embedding) :=
      ctx.map_S ▸ S0.isPGroup'.to_le hp
    exact hm.of_equiv (T.equivMapOfInjective embedding ctx.embedding_injective).symm
  obtain ⟨heq, hn⟩ := base_center ctx.Γ base P hbase hsyl
    (omega_ne_bot T hTp ctx.sectionSeven.S_nontrivial) hcard
  have homega : (omegaOneCenter T).map embedding = omegaOneCenter S := by
    have hm := omegaOneCenterAmbient_map_injective embedding ctx.embedding_injective T
    rw [ctx.map_S] at hm
    exact hm.symm
  have hle : omegaOneCenter S ≤ Q := by
    rw [← homega, ← hmap]
    exact Subgroup.map_mono hn.1
  refine ⟨by rw [heq, homega], ⟨hle, ?_⟩, ?_⟩
  · apply (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    rw [← homega, ← hmap]
    exact (Subgroup.map_mono
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hn.1).mp hn.2)).trans
        (Subgroup.le_normalizer_map embedding)
  · rw [← homega, Subgroup.card_map_of_injective ctx.embedding_injective, ← heq]
    exact hcard

private theorem embedded_transport
    {S0 : Sylow 2 H} {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (base : ctx.Γ.Vertex) (actor : G)
    (hsub : SubnormalIn ((ctx.Γ.e base).map embedding)
      (Subgroup.centralizer ((ctx.Γ.z base).map embedding : Set H)))
    (hchar : IsCharacteristicTwoType
      (Subgroup.centralizer ((ctx.Γ.z base).map embedding : Set H))) :
    SubnormalIn ((ctx.Γ.e (ctx.Γ.act actor base)).map embedding)
      (Subgroup.centralizer ((ctx.Γ.z (ctx.Γ.act actor base)).map embedding : Set H)) ∧
    IsCharacteristicTwoType
      (Subgroup.centralizer ((ctx.Γ.z (ctx.Γ.act actor base)).map embedding : Set H)) := by
  let equiv := MulAut.conj (embedding actor)⁻¹
  have hcomp : embedding.comp (MulAut.conj actor⁻¹).toMonoidHom =
      equiv.toMonoidHom.comp embedding := by
    ext element
    simp [equiv]
  have hZ : (ctx.Γ.z (ctx.Γ.act actor base)).map embedding =
      ((ctx.Γ.z base).map embedding).map equiv.toMonoidHom := by
    rw [z_act, Subgroup.map_map, hcomp, Subgroup.map_map]
  have hE : (ctx.Γ.e (ctx.Γ.act actor base)).map embedding =
      ((ctx.Γ.e base).map embedding).map equiv.toMonoidHom := by
    have hres : ctx.Γ.e (ctx.Γ.act actor base) =
        (ctx.Γ.e base).map (MulAut.conj actor⁻¹).toMonoidHom := by
      change ctx.Γ.twoResidualAt (ctx.Γ.act actor base) =
        (ctx.Γ.twoResidualAt base).map _
      rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoResidualAt_def]
      change twoResidualIn (ctx.Γ.stabilizer (ctx.Γ.act actor base)) =
        (twoResidualIn (ctx.Γ.stabilizer base)).map _
      rw [stabilizer_act]
      exact (map_twoResidualAmbient_of_subgroup_image _ _ _ rfl).symm
    rw [hres, Subgroup.map_map, hcomp, Subgroup.map_map]
  rw [hZ, hE, ← centralizer_map]
  exact ⟨subnormal_map equiv _ _ hsub, characteristicTwo_map_equiv equiv _ hchar⟩

private theorem normalizer_le_centralizer_of_card_two
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) (hK : Nat.card K = 2) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer (K : Set G) := by
  obtain ⟨t, ht_ne, ht_unique⟩ := (Nat.card_eq_two_iff' (1 : K)).mp hK
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  by_cases h1 : k = 1
  · simp [h1]
  have hkt : (⟨k, hk⟩ : K) = t := ht_unique ⟨k, hk⟩ (by
    intro he
    exact h1 (congrArg Subtype.val he))
  have hc : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  have hc1 : g * k * g⁻¹ ≠ 1 := by
    intro he
    have he' := congrArg (fun x : G => g⁻¹ * x * g) he
    exact h1 (by simpa [mul_assoc] using he')
  have hct : (⟨g * k * g⁻¹, hc⟩ : K) = t := ht_unique ⟨_, hc⟩ (by
    intro he
    exact hc1 (congrArg Subtype.val he))
  have he := congrArg (fun x : K => (x : G) * g) (hct.trans hkt.symm)
  simpa [mul_assoc] using he.symm

private theorem ambient_omega
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (hyp : HypothesisTwo H S0 S P1 P2)
    (P : Subgroup H) (hP : P = P1 ∨ P = P2)
    (hn : NormalIn (omegaOneCenter S) P) (hc : Nat.card (omegaOneCenter S) = 2) :
    S = (S0 : Subgroup H) ∧
      SubnormalIn (twoResidualIn P)
        (Subgroup.centralizer (omegaOneCenter S : Set H)) ∧
      IsCharacteristicTwoType (Subgroup.centralizer (omegaOneCenter S : Set H)) := by
  have hSne : omegaOneCenter S ≠ ⊥ := by
    apply (Subgroup.one_lt_card_iff_ne_bot _).mp
    omega
  have hp : IsPGroup 2 (omegaOneCenter S) :=
    (S0.isPGroup'.to_le hyp.fiveOne.S_le_S0).to_le (Subgroup.map_subtype_le _)
  have hnleft (hP2 : P2 ≤ Subgroup.centralizer (omegaOneCenter S : Set H)) :
      ¬ NormalIn (omegaOneCenter S) P1 := by
    intro hn1
    let Z := omegaOneCenter S
    let L := P1 ⊔ P2
    have hZL : Z ≤ L := hn1.1.trans le_sup_left
    have hLnorm : L ≤ Subgroup.normalizer (Z : Set H) := sup_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hn1.1).mp hn1.2)
      (hP2.trans (Subgroup.centralizer_le_normalizer _))
    have hnormal : (Z.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZL).mpr hLnorm
    have hzp : IsPGroup 2 (Z.subgroupOf L) :=
      hp.of_equiv (Subgroup.subgroupOfEquivOfLe hZL).symm
    have hcore : Z ≤ twoCoreIn L := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hZL]
      exact Subgroup.map_mono (show Z.subgroupOf L ≤ pCore 2 L from
        le_sSup ⟨hnormal, hzp⟩)
    exact hSne (le_bot_iff.mp (hcore.trans_eq hyp.fiveOne.join_twoCore_eq_bot))
  have hb : S = (S0 : Subgroup H) ∧ P = P2 ∧
      P2 ∈ PStarFamily (Subgroup.centralizer (omegaOneCenter S : Set H)) S := by
    cases hyp.fiveOne.alternative with
    | a hS hn1 hn2 =>
      rcases hP with rfl | rfl
      · exact (hn1 hn).elim
      · exact (hn2 hn).elim
    | b hS hstar =>
      rcases hP with rfl | rfl
      · exact (hnleft hstar.1.1.1 hn).elim
      · exact ⟨hS, rfl, hstar⟩
    | c _ _ _ hn1 hn2 _ _ _ _ _ _ _ _ =>
      rcases hP with rfl | rfl
      · exact (hn1 hn).elim
      · exact (hn2 hn).elim
  obtain ⟨hS, hPP, hstar⟩ := hb
  subst P
  refine ⟨hS, ?_, ?_⟩
  · have hres := pstar_residual_subnormal_in_omegaCentralizer S0 P2 (hS ▸ hstar)
    simpa only [hS] using hres
  · have hlocal : IsTwoLocal (Subgroup.centralizer (omegaOneCenter S : Set H)) := by
      refine ⟨omegaOneCenter S, hSne, hp, ?_⟩
      exact le_antisymm (Subgroup.centralizer_le_normalizer _)
        (normalizer_le_centralizer_of_card_two _ hc)
    have hSC : (S0 : Subgroup H) ≤
        Subgroup.centralizer (omegaOneCenter S : Set H) := by
      rw [← hS]
      intro element helement
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨inner, ⟨central, hcentral, rfl⟩, rfl⟩ := hz
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp central.property ⟨element, helement⟩).symm
    exact (hyp.hyp1.local_solvable_characteristicTwo _ hlocal hSC).2

/-- An embedded order-two vertex has ambient residual subnormality and a
characteristic-two centralizer, and forces equality with the fixed Sylow. -/
public theorem embedded_orderTwoVertex_residual_subnormal
    {S0 : Sylow 2 H} {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (d : ctx.Γ.Vertex) (hcard : Nat.card (ZAt ctx.Γ d) = 2) :
    S = (S0 : Subgroup H) ∧
      SubnormalIn ((EAt ctx.Γ d).map embedding)
        (Subgroup.centralizer ((ZAt ctx.Γ d).map embedding : Set H)) ∧
      IsCharacteristicTwoType
        (Subgroup.centralizer ((ZAt ctx.Γ d).map embedding : Set H)) := by
  have finish (base : ctx.Γ.Vertex) (P : Subgroup G) (Q : Subgroup H)
      (hbase : ctx.Γ.stabilizer base = P) (hsyl : IsSylowTwoIn T P)
      (hmap : P.map embedding = Q) (hQ : Q = P1 ∨ Q = P2)
      (actor : G) (hd : d = ctx.Γ.act actor base) :
      S = (S0 : Subgroup H) ∧
      SubnormalIn ((EAt ctx.Γ d).map embedding)
        (Subgroup.centralizer ((ZAt ctx.Γ d).map embedding : Set H)) ∧
      IsCharacteristicTwoType
        (Subgroup.centralizer ((ZAt ctx.Γ d).map embedding : Set H)) := by
    have hcardbase : Nat.card (ctx.Γ.z base) = 2 := by
      change Nat.card (ctx.Γ.z d) = 2 at hcard
      rw [hd, z_act, Subgroup.card_map_of_injective
        (MulAut.conj actor⁻¹).injective] at hcard
      exact hcard
    obtain ⟨hZ, hn, hc⟩ := base_image ctx base P Q hbase hsyl hmap hcardbase
    obtain ⟨hS, hsub, hchar⟩ := ambient_omega S0 S P1 P2 ctx.hypothesisTwo Q hQ hn hc
    have hE : (ctx.Γ.e base).map embedding = twoResidualIn Q := by
      change (ctx.Γ.twoResidualAt base).map embedding = _
      rw [ctx.Γ.twoResidualAt_def]
      change (twoResidualIn (ctx.Γ.stabilizer base)).map embedding = _
      rw [hbase]
      exact map_twoResidualAmbient_of_subgroup_image P embedding Q hmap
    rw [← hZ, ← hE] at hsub
    rw [← hZ] at hchar
    exact ⟨hS, hd ▸ embedded_transport ctx base actor hsub hchar⟩
  obtain ⟨actor, hd | hd⟩ := ctx.Γ.coset₁_surjective d
  · exact finish (ctx.Γ.coset₁ 1) A P1
      (base_stabilizer ctx.Γ ctx.Γ.coset₁ A ctx.Γ.act_coset₁ ctx.Γ.coset₁_eq_iff)
      ctx.sectionSeven.P1_mem.1.2.1 ctx.map_P1 (Or.inl rfl) actor
      (by simpa [ctx.Γ.act_coset₁] using hd)
  · exact finish (ctx.Γ.coset₂ 1) B P2
      (base_stabilizer ctx.Γ ctx.Γ.coset₂ B ctx.Γ.act_coset₂ ctx.Γ.coset₂_eq_iff)
      ctx.sectionSeven.P2_mem.1.2.1 ctx.map_P2 (Or.inr rfl) actor
      (by simpa [ctx.Γ.act_coset₂] using hd)

end Stellmacher.SectionNine
