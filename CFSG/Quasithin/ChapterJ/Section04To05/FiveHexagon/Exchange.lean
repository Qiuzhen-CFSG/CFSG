module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.Centralizer
public import Theory.GroupTheory.PrimeSubgroupInvolution
public import Theory.GroupTheory.SubgroupCenterImageBound
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Exchanging source pairs in the Rudvalis five-subgroup hexagon

For the original inverter u, the central involution z inverts C_P(u).
The simultaneous source conjugator carrying (u,C_P(u)) to (z,B₅)
therefore exchanges the two marked pairs. The old base becomes the first
fixed factor of the new canonical core O₅(C_G(C_P(u))). Its other fixed
factor has order five and, together with the old base, generates that
extraspecial group of order 125. It is distinct from all three preceding
five-subgroups; its noncommutation with the old base is proved by order.

All cores, fixed subgroups and conjugators remain inside the original G.
The final existence theorem constructs its inverter from the original
source hypotheses. This supplies the next source row before J.4.8; the
SL₂(5) opposite-pair calculation and six-cycle identification remain the
subsequent J.4.8–10 argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.442–444, using J.3.6.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open Centralizers Centralizers.Choices
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)

omit [Finite G] in
private theorem card_conj (A : Subgroup G) (g : G) : Nat.card (A.conjBy g)=Nat.card A :=
  card_map_of_injective (MulAut.conj g).injective

private theorem z_normalizes_fixed (u : G) (hu : u∈d.toTypeRuSetup.H) :
    c.z∈normalizer (fixedFive B5 u : Set G) := by
  have hzP := G5_normalizes_fiveOddPart B5 (c.z_mem_G5 B5)
  have hzu : Commute c.z u :=
    (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hu)).symm
  have hfor (a:G) (ha:a∈fixedFive B5 u) : c.z*a*c.z⁻¹∈fixedFive B5 u := by
    refine ⟨(mem_normalizer_iff.mp hzP a).mp ha.1,?_⟩
    have h := congrArg (MulAut.conj c.z) (mem_centralizer_singleton_iff.mp ha.2)
    have hu' : MulAut.conj c.z u=u := by
      change c.z*u*c.z⁻¹=u
      rw [hzu.eq,mul_inv_cancel_right]
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul,hu',MulAut.conj_apply] using h
  intro a
  refine ⟨hfor a,fun ha => ?_⟩
  have h := hfor _ ha
  have hz2 := (c.z_involution_of_card d.card_Z).2
  have he : c.z*(c.z*a*c.z⁻¹)*c.z⁻¹=a := by
    calc
      _ = (c.z*c.z)*a*(c.z*c.z)⁻¹ := by group
      _ = a := by rw [← pow_two,hz2]; simp
  rwa [he] at h

theorem base_inverts_fixed (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x∈B5Image B5,u*x*u⁻¹=x⁻¹) :
    ∀ x∈fixedFive B5 u,c.z*x*c.z⁻¹=x⁻¹ := by
  have hc := (source_three_fives c B5 u hu huz hi).1
  rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one (fixedFive B5 u)
    (hc ▸ (by decide : Nat.Prime 5)) c.z
    (c.z_involution_of_card d.card_Z).2 (z_normalizes_fixed c B5 u hu) with hf | hf
  · obtain ⟨q⟩ := c.fiveQuaternionData_source B5
    have hle : fixedFive B5 u≤B5Image B5 := by
      rw [← c.fiveOddPart_inf_centralizer_z d.card_Z B5 q]
      intro x hx
      exact ⟨hx.1,mem_centralizer_singleton_iff.mpr (hf x hx).eq.symm⟩
    have hb : fixedFive B5 u=⊥ := bot_unique ((disjoint_base_fixed c B5 u hi) hle le_rfl)
    rw [hb,card_bot] at hc
    contradiction
  · exact hf

include c in
/-- Every five-subgroup of the original five-centralizer lies in its actual odd core. -/
theorem five_le_oddPart {A : Subgroup G} (hA : Nat.card A=5) (hAG : A≤G5 B5) :
    A≤fiveOddPart B5 := by
  let N := pPrimeCore 2 (G5 B5)
  let f : A →* (G5 B5) ⧸ N := (QuotientGroup.mk' N).comp (inclusion hAG)
  have hNc : Nat.card N=125 := by
    have h := SourceCompletion.five_oddPart_card c B5
    rw [card_map_of_injective (G5 B5).subtype_injective] at h
    exact h
  have hG5 : Nat.card (G5 B5)=1000 := by
    obtain ⟨q⟩ := c.fiveQuaternionData_source B5
    rw [G5_card c B5 d.card_Z q,SourceCompletion.five_oddPart_card c B5]
  have hQc : Nat.card ((G5 B5) ⧸ N)=8 := by
    have h := card_eq_card_quotient_mul_card_subgroup N
    rw [hNc,hG5] at h
    omega
  have hd1 : Nat.card f.range∣5 := hA ▸ Subgroup.card_range_dvd f
  have hd2 : Nat.card f.range∣8 := hQc ▸ f.range.card_subgroup_dvd_card
  have hc : Nat.card f.range=1 := Nat.dvd_one.mp (Nat.dvd_gcd hd1 hd2)
  have hb : f.range=⊥ := card_eq_one.mp hc
  intro x hx
  have he : f ⟨x,hx⟩=1 := mem_bot.mp (hb ▸ (show f ⟨x,hx⟩∈f.range from ⟨⟨x,hx⟩,rfl⟩))
  have hm : (⟨x,hAG hx⟩:G5 B5)∈N := (QuotientGroup.eq_one_iff _).mp he
  exact mem_map_of_mem (G5 B5).subtype hm

/-- The canonical five-core attached to any of the original five-subgroups. -/
abbrev coreAt (B : Subgroup G) : Subgroup G := pCoreIn 5 (centralizer (B : Set G))

omit [Finite G] in
theorem map_coreAt (B : Subgroup G) (e : G ≃* G) :
    (coreAt B).map e.toMonoidHom = coreAt (B.map e.toMonoidHom) := by
  rw [coreAt,map_pCoreIn_of_injective 5 _ _ e.injective,Theory.Quasithin.map_centralizer]

include c in
theorem coreAt_base : coreAt (B5Image B5)=fiveOddPart B5 :=
  (SourceCompletion.five_oddPart_eq_core c B5).symm

/-- Simultaneous conjugacy transports the core, center and fixed subgroup
through the actual conjugating element, leaving a canonical ambient core. -/
theorem pair_core (A : Subgroup G) (v g : G)
    (hv : g*v*g⁻¹=c.z) (hA : A.conjBy g=B5Image B5) :
    (coreAt A).conjBy g=fiveOddPart B5 ∧ Nat.card (coreAt A)=125 ∧
      (center (coreAt A)).map (coreAt A).subtype=A ∧
      coreAt A ⊓ centralizer ({v}:Set G)=A := by
  have hm : (coreAt A).conjBy g=fiveOddPart B5 := by
    change (coreAt A).map (MulAut.conj g).toMonoidHom=_
    rw [map_coreAt]
    change coreAt (A.conjBy g)=_
    rw [hA,coreAt_base c B5]
  have hcard : Nat.card (coreAt A)=125 := by
    have he := congrArg (fun S : Subgroup G => Nat.card S) hm
    rw [card_conj] at he
    exact he.trans (SourceCompletion.five_oddPart_card c B5)
  have hcenter : (center (coreAt A)).map (coreAt A).subtype=A := by
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [map_subgroup_center_eq _ (MulAut.conj g).injective]
    change (center ((coreAt A).conjBy g)).map ((coreAt A).conjBy g).subtype=A.conjBy g
    rw [hm,hA,Section03.five_oddPart_center c B5 (Section03.order_source c)]
  have hfixed : coreAt A ⊓ centralizer ({v}:Set G)=A := by
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [map_inf _ _ _ (MulAut.conj g).injective,
      Theory.GroupTheory.map_centralizer_singleton]
    change (coreAt A).conjBy g ⊓ centralizer ({g*v*g⁻¹}:Set G)=A.conjBy g
    rw [hm,hv,hA]
    obtain ⟨q⟩ := c.fiveQuaternionData_source B5
    exact c.fiveOddPart_inf_centralizer_z d.card_Z B5 q
  exact ⟨hm,hcard,hcenter,hfixed⟩

/-- The canonical core at any simultaneously marked source pair is extraspecial. -/
theorem pair_core_extraspecial (A : Subgroup G) (v g : G)
    (hv : g*v*g⁻¹=c.z) (hA : A.conjBy g=B5Image B5) :
    IsExtraspecial 5 (coreAt A) := by
  have hm := (pair_core c B5 A v g hv hA).1
  have h : IsExtraspecial 5 ((coreAt A).conjBy g) :=
    hm.symm ▸ Section03.five_oddPart_extraspecial c B5 (Section03.order_source c)
  exact IsExtraspecial.of_mulEquiv ((MulAut.conj g).subgroupMap (coreAt A)).symm h

/-- Exchange the two commuting source pairs using the same simultaneous
conjugator. The old base becomes the first fixed factor of the new core. -/
theorem swapped_seed (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x∈B5Image B5,u*x*u⁻¹=x⁻¹) :
    ∃ g:G, g*u*g⁻¹=c.z ∧ (fixedFive B5 u).conjBy g=B5Image B5 ∧
      g*c.z*g⁻¹∈d.toTypeRuSetup.H ∧ IsConj (g*c.z*g⁻¹) c.z ∧
      (∀ x∈B5Image B5,(g*c.z*g⁻¹)*x*(g*c.z*g⁻¹)⁻¹=x⁻¹) ∧
      (B5Image B5).conjBy g=fixedFive B5 (g*c.z*g⁻¹) := by
  have h5 := (source_three_fives c B5 u hu huz hi).1
  obtain ⟨g,hgu,hgA⟩ := pair_conjugacy c B5 u huz h5
  let e := MulAut.conj g
  let v := e c.z
  have hgu' : e u=c.z := hgu
  have hvH : v∈d.toTypeRuSetup.H := by
    rw [c.H_eq_centralizer_z,mem_centralizer_singleton_iff]
    have hzu := mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hu)
    have he := congrArg e hzu.symm
    simpa only [map_mul,hgu'] using he
  have hvclass : IsConj v c.z := (isConj_iff.mpr ⟨g,rfl⟩ : IsConj c.z v).symm
  have hinv : ∀ x∈B5Image B5,v*x*v⁻¹=x⁻¹ := by
    intro x hx
    rw [← hgA] at hx
    obtain ⟨a,ha,rfl⟩ := hx
    have he := congrArg e (base_inverts_fixed c B5 u hu huz hi a ha)
    simpa only [map_mul,map_inv,v,e,MulEquiv.coe_toMonoidHom] using he
  have hDP : (B5Image B5).conjBy g≤fiveOddPart B5 := by
    apply five_le_oddPart c B5
    · exact (card_map_of_injective e.injective).trans (B5Image_card d.card_Z B5)
    · rintro x ⟨b,hb,rfl⟩ a ha
      rw [← hgA] at ha
      obtain ⟨w,hw,rfl⟩ := ha
      have he := congrArg e (central_edge B5 u hb w hw)
      simpa only [map_mul,v,e,MulEquiv.coe_toMonoidHom] using he
  have hle : (B5Image B5).conjBy g≤fixedFive B5 v := by
    intro x hx
    refine ⟨hDP hx,?_⟩
    obtain ⟨a,ha,rfl⟩ := hx
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg e (c.z_mem_G5 B5 a ha)
    simpa only [map_mul,v,e,MulEquiv.coe_toMonoidHom] using he
  have heq : (B5Image B5).conjBy g=fixedFive B5 v :=
    eq_of_le_of_card_ge hle (by
      rw [card_conj,B5Image_card d.card_Z B5,
        (source_three_fives c B5 v hvH hvclass hinv).1])
  exact ⟨g,hgu,hgA,hvH,hvclass,hinv,heq⟩

/-- The next five-subgroup is defined inside the canonical core of C_P(u),
not by a new abstract extraspecial witness. -/
abbrev nextFive (u : G) : Subgroup G :=
  coreAt (fixedFive B5 u) ⊓ centralizer ({c.z*u}:Set G)

/-- The source exchange constructs the fourth vertex, with its literal
centralizer, two adjacent factors and noncommuting opposite factor. -/
theorem next_five_structure (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x∈B5Image B5,u*x*u⁻¹=x⁻¹) :
    Nat.card (nextFive c B5 u)=5 ∧
      Nat.card (coreAt (fixedFive B5 u))=125 ∧
      (center (coreAt (fixedFive B5 u))).map (coreAt (fixedFive B5 u)).subtype=
        fixedFive B5 u ∧
      B5Image B5 ⊔ nextFive c B5 u=coreAt (fixedFive B5 u) ∧
      fixedFive B5 u≤centralizer (nextFive c B5 u : Set G) ∧
      ¬ B5Image B5≤centralizer (nextFive c B5 u : Set G) := by
  obtain ⟨g,hgu,hgA,hvH,hvclass,hinv,hBmap⟩ := swapped_seed c B5 u hu huz hi
  let v := g*c.z*g⁻¹
  obtain ⟨hPmap,hPc,hPZ,hPf⟩ := pair_core c B5 (fixedFive B5 u) u g hgu hgA
  have hprod : g*(c.z*u)*g⁻¹=c.z*v := by
    have he := (MulAut.conj g).map_mul c.z u
    change g*(c.z*u)*g⁻¹=(g*c.z*g⁻¹)*(g*u*g⁻¹) at he
    rw [hgu] at he
    exact he.trans (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hvH))
  have hCmap : (nextFive c B5 u).conjBy g=fixedFive B5 (c.z*v) := by
    change (coreAt (fixedFive B5 u) ⊓ centralizer ({c.z*u}:Set G)).map
      (MulAut.conj g).toMonoidHom=_
    rw [map_inf _ _ _ (MulAut.conj g).injective,Theory.GroupTheory.map_centralizer_singleton]
    change (coreAt (fixedFive B5 u)).conjBy g ⊓
      centralizer ({g*(c.z*u)*g⁻¹}:Set G)=_
    rw [hPmap,hprod]
  have hs := source_three_fives c B5 v hvH hvclass hinv
  have hCc : Nat.card (nextFive c B5 u)=5 := by
    have he := congrArg (fun A:Subgroup G => Nat.card A) hCmap
    rw [card_conj] at he
    exact he.trans hs.2.1
  have hgen : B5Image B5 ⊔ nextFive c B5 u=coreAt (fixedFive B5 u) := by
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [Subgroup.map_sup]
    change (B5Image B5).conjBy g ⊔ (nextFive c B5 u).conjBy g=
      (coreAt (fixedFive B5 u)).conjBy g
    rw [hBmap,hCmap,hPmap]
    exact generated_by_fixed_pair c B5 v hvH (product_class c B5 v hvH hvclass hinv).1 hinv
  have hcent : fixedFive B5 u≤centralizer (nextFive c B5 u : Set G) := by
    intro a ha b hb
    rw [← hPZ] at ha
    obtain ⟨a,ha,rfl⟩ := ha
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨b,hb.1⟩)
  refine ⟨hCc,hPc,hPZ,hgen,hcent,?_⟩
  intro hcomm
  have hsmall : Nat.card (B5Image B5 ⊔ nextFive c B5 u : Subgroup G)≤25 := by
    have hnormal : nextFive c B5 u≤normalizer (B5Image B5 : Set G) :=
      (le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _)
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
      (B5Image B5) (nextFive c B5 u) hnormal
    rw [B5Image_card d.card_Z B5,hCc] at hc
    have hp : 0<Nat.card (B5Image B5 ⊓ nextFive c B5 u : Subgroup G) := Nat.card_pos
    nlinarith
  rw [hgen,hPc] at hsmall
  omega

omit [Finite G] in
private theorem ne_of_disjoint_five {A B : Subgroup G}
    (hd : Disjoint A B) (hA : Nat.card A=5) : A≠B := by
  rintro rfl
  have he : A=⊥ := bot_unique (hd le_rfl le_rfl)
  rw [he,card_bot] at hA
  contradiction

/-- The first four actual vertices in the source commuting hexagon. -/
noncomputable def fourFives (u : G) : Finset (Subgroup G) := by
  classical
  exact {B5Image B5,fixedFive B5 u,fixedFive B5 (c.z*u),nextFive c B5 u}

/-- The new fixed factor is distinct from all three preceding source fives. -/
theorem four_fives_card (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x∈B5Image B5,u*x*u⁻¹=x⁻¹) :
    (fourFives c B5 u).card=4 := by
  classical
  have hs := source_three_fives c B5 u hu huz hi
  have hn := next_five_structure c B5 u hu huz hi
  have hBA := ne_of_disjoint_five hs.2.2.1 (B5Image_card d.card_Z B5)
  have hAD := ne_of_disjoint_five hs.2.2.2.1 hs.1
  have hBD := ne_of_disjoint_five hs.2.2.2.2.1 (B5Image_card d.card_Z B5)
  have hCB : nextFive c B5 u≠B5Image B5 := by
    intro he
    apply hn.2.2.2.2.2
    rw [he]
    exact B5Image_le_G5 d.card_Z B5
  have hCA : nextFive c B5 u≠fixedFive B5 u := by
    intro he
    apply hn.2.2.2.2.2
    rw [he]
    exact central_edge B5 u
  have hCD : nextFive c B5 u≠fixedFive B5 (c.z*u) := by
    intro he
    apply hn.2.2.2.2.2
    rw [he]
    exact central_edge B5 (c.z*u)
  simp [fourFives,hBA,hBD,hAD,hCB.symm,hCA.symm,hCD.symm]

/-- The original source supplies an inverter and hence four distinct
canonical five-subgroups, without any geometric-model premise. -/
theorem exists_source_four_fives :
    ∃ u:G, u∈d.toTypeRuSetup.H ∧ IsConj u c.z ∧
      (∀ x∈B5Image B5,u*x*u⁻¹=x⁻¹) ∧ (fourFives c B5 u).card=4 ∧
      Nat.card (nextFive c B5 u)=5 ∧
      B5Image B5 ⊔ nextFive c B5 u=coreAt (fixedFive B5 u) ∧
      ¬B5Image B5≤centralizer (nextFive c B5 u : Set G) := by
  obtain ⟨r⟩ := c.fiveInverterData_source B5
  have hn := next_five_structure c B5 r.i r.mem_H r.z_class r.inverts
  exact ⟨r.i,r.mem_H,r.z_class,r.inverts,
    four_fives_card c B5 r.i r.mem_H r.z_class r.inverts,hn.1,hn.2.2.2.1,hn.2.2.2.2.2⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
