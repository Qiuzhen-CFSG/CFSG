module
public import Theory.Alternating.FivePairBorel
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.Hall.Basic

/-!
# Actual odd Hall tori above an A₅ pair

The normalizer of a Sylow two-subgroup of A₅ × A₅ has order 144. A surjection
with two-group kernel lifts this normalizer exactly. A Sylow three-subgroup
there contains any prescribed three-subgroup, has order nine, and is an odd
Hall subgroup. Its two A₅ coordinates have exponent three, so the actual
lifted subgroup is elementary abelian of order nine.

Source application: Aschbacher–Smith, 10.2.3, printed pp.745–746.
The construction retains the original subgroup and the full two-group kernel.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.AlternatingFive
local notation "A" => alternatingGroup (Fin 5)

private theorem single_normalizer_card (P : Sylow 2 A) :
    Nat.card (normalizer (P : Set A)) = 12 := by
  obtain ⟨i,hi⟩ :=
    Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P
  rw [hi,Nat.card_eq_fintype_card]
  clear hi P
  revert i
  decide +kernel

private theorem pair_sylow_product (P : Sylow 2 (A × A)) :
    ∃ Q R : Sylow 2 A, (P : Subgroup (A × A)) =
      (Q : Subgroup A).prod (R : Subgroup A) := by
  let Q := P.mapSurjective (f := MonoidHom.fst A A) (fun x => ⟨(x,1),rfl⟩)
  let R := P.mapSurjective (f := MonoidHom.snd A A) (fun x => ⟨(1,x),rfl⟩)
  have htwo : IsPGroup 2 ((Q : Subgroup A).prod (R : Subgroup A)) := by
    obtain ⟨a,ha⟩ := Q.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := R.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := a+b) (by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,ha,hb,pow_add])
  refine ⟨Q,R,(P.is_maximal' htwo ?_).symm⟩
  intro x hx
  exact ⟨mem_map_of_mem (MonoidHom.fst A A) hx,mem_map_of_mem (MonoidHom.snd A A) hx⟩

theorem pair_sylow_normalizer_card (S : Sylow 2 (A × A)) :
    Nat.card (normalizer (S : Set (A × A))) = 144 := by
  obtain ⟨Q,R,hS⟩ := pair_sylow_product S
  have hn : normalizer ((Q : Subgroup A).prod (R : Subgroup A) : Set (A × A)) =
      (normalizer ((Q : Subgroup A) : Set A)).prod
        (normalizer ((R : Subgroup A) : Set A)) := by
    ext g
    simp only [Subgroup.mem_prod,Subgroup.mem_normalizer_iff]
    constructor
    · intro h
      exact ⟨fun x => by simpa using h (x,1),fun y => by simpa using h (1,y)⟩
    · rintro ⟨hQ,hR⟩ ⟨x,y⟩
      exact (hQ x).and (hR y)
  rw [show (S : Set (A × A)) = ((Q : Subgroup A).prod (R : Subgroup A) : Set (A × A))
      from congrArg SetLike.coe hS,hn,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod]
  have hQ : Nat.card (normalizer ((Q : Subgroup A) : Set A)) = 12 := by
    simpa only [Sylow.coe_coe] using single_normalizer_card Q
  have hR : Nat.card (normalizer ((R : Subgroup A) : Set A)) = 12 := by
    simpa only [Sylow.coe_coe] using single_normalizer_card R
  rw [hQ,hR]

theorem three_subgroup_card_dvd_three (P : Subgroup A) (hP : IsPGroup 3 P) :
    Nat.card P ∣ 3 := by
  obtain ⟨n,hn⟩ := hP.exists_card_eq
  have hc : Nat.Coprime (Nat.card P) 20 := hn ▸ (by decide : Nat.Coprime 3 20).pow_left n
  apply hc.dvd_of_dvd_mul_left
  have hd := P.card_subgroup_dvd_card
  rw [nat_card_alternatingGroup] at hd
  norm_num [Nat.factorial] at hd ⊢
  exact hd

/-- A quotient with two-group kernel is faithful on every actual three-subgroup. -/
theorem injective_on_three_subgroup
    {G K : Type*} [Group G] [Group K]
    (q : G →* K) (hk : IsPGroup 2 q.ker) (D : Subgroup G) (hD : IsPGroup 3 D) :
    Function.Injective (q.comp D.subtype) := by
  have hd := IsPGroup.disjoint_of_coprime hk hD (by decide : Nat.Coprime 2 3)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply Subtype.ext
  exact disjoint_def.mp hd hx x.property

theorem three_subgroup_cube_eq_one
    {G : Type*} [Group G] (q : G →* A × A) (hk : IsPGroup 2 q.ker)
    (D : Subgroup G) (hD : IsPGroup 3 D) (d : D) : d ^ 3 = 1 := by
  have hinj := injective_on_three_subgroup q hk D hD
  apply hinj
  rw [map_pow,map_one]
  apply Prod.ext
  · let P := D.map ((MonoidHom.fst A A).comp q)
    have hP : IsPGroup 3 P := hD.map _
    have hc := three_subgroup_card_dvd_three P hP
    have hp := pow_card_eq_one' (x := (⟨(q d).1,mem_map_of_mem _ d.property⟩ : P))
    obtain ⟨k,hk⟩ := hc
    have hh : (⟨(q d).1,mem_map_of_mem _ d.property⟩ : P) ^ 3 = 1 := by
      rw [hk,pow_mul,hp,one_pow]
    exact congrArg Subtype.val hh
  · let P := D.map ((MonoidHom.snd A A).comp q)
    have hP : IsPGroup 3 P := hD.map _
    have hc := three_subgroup_card_dvd_three P hP
    have hp := pow_card_eq_one' (x := (⟨(q d).2,mem_map_of_mem _ d.property⟩ : P))
    obtain ⟨k,hk⟩ := hc
    have hh : (⟨(q d).2,mem_map_of_mem _ d.property⟩ : P) ^ 3 = 1 := by
      rw [hk,pow_mul,hp,one_pow]
    exact congrArg Subtype.val hh

private theorem three_sylow_oddHall
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 6 G) (P : Sylow 3 G) :
    IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} (P : Subgroup G) := by
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  have ho : Odd (Nat.card P) := by
    rw [hn]
    exact (show Odd 3 by decide).pow
  refine isHallSubgroup_of _ _ ?_ ?_
  · intro p hp he
    exact ho.not_two_dvd_nat (he ▸ hp)
  · intro p hp hi
    obtain ⟨m,hm⟩ := hG.exists_card_dvd_pow
    have hd := p.property.dvd_of_dvd_pow ((hi.trans P.index_dvd_card).trans hm)
    rcases p.property.dvd_mul.mp (show p.val ∣ 2 * 3 from hd) with htwo | hthree
    · exact hp ((Nat.prime_two.eq_one_or_self_of_dvd p.val htwo).resolve_left p.property.ne_one)
    · have he := (Nat.prime_three.eq_one_or_self_of_dvd p.val hthree).resolve_left p.property.ne_one
      rw [he] at hi
      exact P.not_dvd_index hi

theorem exists_three_torus_in_sylow_normalizer
    {G : Type*} [Group G] [Finite G]
    (q : G →* A × A) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (S : Sylow 2 G) (B : Subgroup G) (hB : IsPGroup 3 B)
    (hBN : B ≤ normalizer (S : Set G)) :
    ∃ D : Subgroup G, B ≤ D ∧ D ≤ normalizer (S : Set G) ∧
      IsHallSubgroup {p : Nat.Primes | p.val ≠ 2}
        (D.subgroupOf (normalizer (S : Set G))) ∧
      Nat.card D = 9 ∧ IsElementaryAbelian 3 D := by
  let N := normalizer (S : Set G)
  let Q := S.mapSurjective hq
  let NQ := normalizer (Q : Set (A × A))
  have hcore : q.ker ≤ (S : Subgroup G) := hk.le_sylow_of_normal S
  have hpre : NQ.comap q = N := by
    change (normalizer ((S : Subgroup G).map q : Set _)).comap q = _
    rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hcore]
    rfl
  let f : N →* NQ := (q.comp N.subtype).codRestrict NQ (fun x =>
    (le_normalizer_map q) (mem_map_of_mem q x.property))
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨x,hx⟩ := hq z
    have hxN : x ∈ N := by
      rw [←hpre]
      change q x ∈ NQ
      rw [hx]
      exact z.property
    exact ⟨⟨x,hxN⟩,Subtype.ext hx⟩
  have hfker : IsPGroup 2 f.ker :=
    (hk.comap_subtype (K := N)).to_le (fun x hx => congrArg Subtype.val hx)
  have hNQ6 : IsPGroup 6 NQ := IsPGroup.of_card_dvd_pow (n := 4) (by
    rw [pair_sylow_normalizer_card Q]
    decide)
  have hN6 : IsPGroup 6 N := by
    have hh := (hNQ6.to_subgroup ⊤).comap_of_ker_isPGroup f
      (hfker.mono (by decide : 2 ∣ 6))
    simpa only [comap_top] using hh.of_equiv Subgroup.topEquiv
  obtain ⟨P,hP⟩ := (hB.comap_subtype (K := N)).exists_le_sylow
  let PQ := P.mapSurjective hf
  have hPQ : Nat.card PQ = 9 := by
    rw [PQ.card_eq_multiplicity]
    rw [pair_sylow_normalizer_card Q]
    decide +kernel
  have hPinj := injective_on_three_subgroup f hfker (P : Subgroup N) P.isPGroup'
  have hPc : Nat.card P = 9 := by
    have hc := Nat.card_congr (MonoidHom.ofInjective hPinj).toEquiv
    have hr : (f.comp (P : Subgroup N).subtype).range = (PQ : Subgroup NQ) := by
      rw [MonoidHom.range_comp,range_subtype]
      rfl
    rw [hr] at hc
    exact hc.trans hPQ
  let D := (P : Subgroup N).map N.subtype
  have hDc : Nat.card D = 9 := by
    rw [card_map_of_injective N.subtype_injective]
    exact hPc
  have hD3 : IsPGroup 3 D := P.isPGroup'.map N.subtype
  refine ⟨D,?_,map_subtype_le _,?_,hDc,?_⟩
  · intro b hb
    exact ⟨⟨b,hBN hb⟩,hP hb,rfl⟩
  · have he : D.subgroupOf N = (P : Subgroup N) :=
      comap_map_eq_self_of_injective N.subtype_injective _
    rw [he]
    exact three_sylow_oddHall hN6 P
  · exact { toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq
              (p := 3) (by simpa using hDc)
            exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
              (three_subgroup_cube_eq_one q hk D hD3) }

end Theory.AlternatingFive
