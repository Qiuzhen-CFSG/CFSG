module

public import Glauberman.DicksonClassification
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import GorensteinWalter.PGL2Cardinality
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import BenderSuzuki.External.Huppert.II.theorem_8_27
public import GorensteinWalter.OddSubgroupLeNormalIndexTwo
import Mathlib.Tactic

/-!
# Sylow thirteen overgroups in PSL₂(25) and index-two extensions

Dickson's actual subgroup classification reduces a proper subgroup of
PSL₂(25) with order divisible by thirteen to order thirteen or twenty-six.
The nonsplit torus and Sylow conjugacy give normalizer order twenty-six.
In any normal index-two extension, Frattini's argument doubles that order;
socle-avoiding overgroups have orders thirteen, twenty-six or fifty-two
and normalize the Sylow subgroup. The socle-avoidance condition is essential:
the core itself is a proper index-two overgroup.

This is the native thirteen-subgroup input for Aschbacher--Smith J.5.5(5),
printed p.447, with the actual mixed extension instantiated separately.
-/

public section

noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.PSL2.TwentyFive
variable {F : Type*} [Field F] [Finite F]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

theorem card (hF : Nat.card F=25) : Nat.card (PSL2MatrixGroup F)=7800 := by
  have h := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ (by decide : Odd 25))
  rw [hF] at h
  change Nat.card (PSL2MatrixGroup F) * 2 = 25 * (25^2-1) at h
  omega

theorem proper_thirteen_subgroup_card (hF : Nat.card F=25)
    (H : Subgroup (PSL2MatrixGroup F)) (hne : H≠⊤) (h13 : 13∣Nat.card H) :
    Nat.card H=13 ∨ Nat.card H=26 := by
  have hFp : Nat.card F=5^2 := hF
  have hcop : Nat.Coprime 13 5 := by decide
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hFp H with
    hElem | hCyc | hDih | hA4 | hS4 | hA5 | hBorel | hPSL | hPGL
  · let : IsElementaryAbelian 5 H := hElem
    obtain ⟨m,hm⟩ := (IsElementaryAbelian.isPGroup 5 H).exists_card_eq
    rw [hm] at h13
    have := (hcop.pow_right m).eq_one_of_dvd h13
    norm_num at this
  · obtain ⟨z,hz,hc,_⟩ := hCyc
    norm_num [hF] at hz
    rw [hc] at h13
    rcases hz with hz|hz
    · have hh := dvd_trans h13 hz
      norm_num at hh
    · have he := Nat.dvd_antisymm hz h13
      exact Or.inl (hc.trans he)
  · obtain ⟨z,hz,hc,_⟩ := hDih
    norm_num [hF] at hz
    have hz13 : 13∣z := by
      rw [hc] at h13
      exact (show Nat.Coprime 13 2 from by decide).dvd_of_dvd_mul_left h13
    rcases hz with hz|hz
    · have hh := dvd_trans hz13 hz
      norm_num at hh
    · have he := Nat.dvd_antisymm hz hz13
      exact Or.inr (by simpa [he] using hc)
  · obtain ⟨_,⟨e⟩⟩ := hA4
    have hc := Nat.card_congr e.toEquiv
    rw [nat_card_alternatingGroup,Nat.card_fin] at hc
    norm_num at hc
    norm_num [hc] at h13
  · obtain ⟨_,⟨e⟩⟩ := hS4
    have hc := Nat.card_congr e.toEquiv
    rw [Nat.card_perm,Nat.card_fin] at hc
    norm_num at hc
    norm_num [hc] at h13
  · obtain ⟨_,⟨e⟩⟩ := hA5
    have hc := Nat.card_congr e.toEquiv
    rw [nat_card_alternatingGroup,Nat.card_fin] at hc
    norm_num at hc
    norm_num [hc] at h13
  · obtain ⟨m,t,_,ht,N,C,hN,_,hcN,_,hcC,hdisj,hsup⟩ := hBorel
    let : N.Normal := hN
    have hc : Nat.card H=5^m*t := by
      have hh := card_sup_eq_mul_of_normalizes_of_disjoint N C
        (by rw [N.normalizer_eq_top];exact le_top) hdisj
      simpa [hsup,hcN,hcC] using hh
    rw [hc] at h13
    have ht13 := (hcop.pow_right m).dvd_of_dvd_mul_left h13
    norm_num at ht
    have hh := dvd_trans ht13 ht
    norm_num at hh
  · obtain ⟨m,hm0,hmdiv,⟨e⟩⟩ := hPSL
    have hm : m=1 ∨ m=2 := (Nat.dvd_prime Nat.prime_two).mp hmdiv
    rcases hm with rfl|rfl
    · have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
        (F := GaloisField 5 1) (by rw [GaloisField.card 5 1 (by decide)];decide)
      rw [GaloisField.card 5 1 (by decide),←Nat.card_congr e.toEquiv] at hc
      norm_num at hc
      have h60 : Nat.card H=60 := by omega
      norm_num [h60] at h13
    · exact (hne (eq_top_of_card_eq H ((Nat.card_congr e.toEquiv).trans
        (by rw [card (GaloisField.card 5 2 (by decide)),card hF])))).elim
  · obtain ⟨m,hm0,hmdiv,⟨e⟩⟩ := hPGL
    have hmpos : 0<m := Nat.pos_of_ne_zero hm0
    have hbound := Nat.le_of_dvd (by decide : 0<2) hmdiv
    have hm : m=1 := by omega
    subst m
    have hc := GorensteinWalter.pgl2_card_formula (GaloisField 5 1)
    rw [GaloisField.card 5 1 (by decide),←Nat.card_congr e.toEquiv] at hc
    norm_num at hc
    norm_num [hc] at h13

theorem sylow_thirteen_normalizer_card (hF : Nat.card F=25) (P : Sylow 13 (PSL2MatrixGroup F)) :
    Nat.card (normalizer (P : Set (PSL2MatrixGroup F)))=26 := by
  obtain ⟨S,_,hS,hN⟩ := BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_normalizer_card
    (F := F) (p := 5) (f := 2) hF
  norm_num [hF] at hS
  let Q : Sylow 13 (PSL2MatrixGroup F) := Sylow.ofCard S (by rw [hS,card hF];decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (PSL2MatrixGroup F) Q P
  have hmap : (P : Subgroup (PSL2MatrixGroup F))=S.map (MulAut.conj g).toMonoidHom := by
    rw [←hg]
    change (Q : Subgroup _).map (MulAut.conj g).toMonoidHom=_
    rw [Sylow.coe_ofCard]
  change Nat.card (normalizer ((P : Subgroup (PSL2MatrixGroup F)) : Set (PSL2MatrixGroup F)))=26
  rw [hmap,← Subgroup.map_equiv_normalizer_eq,card_map_of_injective (MulAut.conj g).injective,hN,hS]


namespace IndexTwo
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem card_subgroupOf_swap (A B : Subgroup G) :
    Nat.card (A.subgroupOf B)=Nat.card (B.subgroupOf A) := by
  rw [←inf_subgroupOf_right A B,←inf_subgroupOf_left B A]
  exact (Nat.card_congr (subgroupOfEquivOfLe (show A⊓B≤B from inf_le_right)).toEquiv).trans
    (Nat.card_congr (subgroupOfEquivOfLe (show A⊓B≤A from inf_le_left)).toEquiv).symm

variable (N : Subgroup G) [N.Normal] (hN : N.index=2)
variable (e : N ≃* PSL2MatrixGroup F) (hF : Nat.card F=25)

include hN e hF

omit [N.Normal] [Finite G] in
theorem card_group : Nat.card G=15600 := by
  have hc : Nat.card N=7800 := (Nat.card_congr e.toEquiv).trans (card hF)
  have h := N.card_mul_index
  rw [hc,hN] at h
  exact h.symm

omit [N.Normal] in
theorem sylow_card (P : Sylow 13 G) : Nat.card P=13 := by
  rw [P.card_eq_multiplicity,card_group N hN e hF]
  decide +kernel

theorem sylow_le (P : Sylow 13 G) : (P : Subgroup G)≤N :=
  GorensteinWalter.odd_card_subgroup_le_normal_index_two N P inferInstance hN
    (by rw [sylow_card N hN e hF P];decide)


theorem normalizer_card (P : Sylow 13 G) : Nat.card (normalizer (P : Set G))=52 := by
  have hPN := sylow_le N hN e hF P
  let Q : Sylow 13 N := P.subtype hPN
  let R : Sylow 13 (PSL2MatrixGroup F) := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR := sylow_thirteen_normalizer_card hF R
  have hcore : Nat.card ((normalizer (P : Set G)).subgroupOf N)=26 := by
    change Nat.card ((normalizer ((P : Subgroup G) : Set G)).subgroupOf N)=26
    rw [subgroupOf_normalizer_eq hPN]
    change Nat.card (normalizer (Q : Set N))=26
    change Nat.card (normalizer (((Q : Subgroup N).map e.toMonoidHom : Subgroup (PSL2MatrixGroup F)) : Set (PSL2MatrixGroup F)))=26 at hR
    rw [←map_equiv_normalizer_eq,card_map_of_injective e.injective] at hR
    exact hR
  have hi : N.relIndex (normalizer (P : Set G))=2 := by
    rw [←relIndex_sup_right, P.normalizer_sup_eq_top' hPN,relIndex_top_right,hN]
  have hc := (N.subgroupOf (normalizer (P : Set G))).card_mul_index
  rw [←card_subgroupOf_swap, hcore] at hc
  change 26 * N.relIndex (normalizer (P : Set G)) = _ at hc
  rw [hi] at hc
  exact hc.symm

theorem overgroup_card (P : Sylow 13 G) (H : Subgroup G)
    (hPH : (P : Subgroup G)≤H) (hNH : ¬N≤H) :
    Nat.card H=13 ∨ Nat.card H=26 ∨ Nat.card H=52 := by
  let J : Subgroup N := H.subgroupOf N
  have hJ : J≠⊤ := by
    intro he
    exact hNH (subgroupOf_eq_top.mp he)
  have h13 : 13∣Nat.card J := by
    have hPN := sylow_le N hN e hF P
    have hpj : (P : Subgroup G).subgroupOf N≤J := subgroupOf_mono N hPH
    have hp := card_dvd_of_le hpj
    rwa [Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv,sylow_card N hN e hF P] at hp
  have hJmap : J.map e.toMonoidHom≠⊤ := by
    intro htop
    have hh := congrArg (fun K => K.comap e.toMonoidHom) htop
    apply hJ
    simpa only [comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective,comap_top] using hh
  have hJcard := proper_thirteen_subgroup_card hF (J.map e.toMonoidHom) hJmap
    (by rwa [card_map_of_injective e.injective])
  rw [card_map_of_injective e.injective] at hJcard
  have hi := N.relIndex_dvd_index_of_normal H
  rw [hN,Nat.dvd_prime Nat.prime_two] at hi
  have hc := (N.subgroupOf H).card_mul_index
  rw [←card_subgroupOf_swap H N] at hc
  change Nat.card J * N.relIndex H = Nat.card H at hc
  rcases hJcard with h|h <;> rcases hi with hi|hi <;> simp_all

theorem overgroup_index (P : Sylow 13 G) (H : Subgroup G)
    (hPH : (P : Subgroup G)≤H) (hNH : ¬N≤H) :
    H.index=300 ∨ H.index=600 ∨ H.index=1200 := by
  have hc := H.card_mul_index
  rw [card_group N hN e hF] at hc
  rcases overgroup_card N hN e hF P H hPH hNH with h|h|h <;> rw [h] at hc <;> omega

theorem overgroup_le_normalizer (P : Sylow 13 G) (H : Subgroup G)
    (hPH : (P : Subgroup G)≤H) (hNH : ¬N≤H) : H≤normalizer (P : Set G) := by
  let Q : Sylow 13 H := P.subtype hPH
  have hqcard : Nat.card Q=13 :=
    (Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv).trans (sylow_card N hN e hF P)
  have hindex : Q.index≤4 := by
    have hc := Q.toSubgroup.card_mul_index
    rw [hqcard] at hc
    rcases overgroup_card N hN e hF P H hPH hNH with h|h|h <;> rw [h] at hc <;> omega
  have hcount : Nat.card (Sylow 13 H)≤4 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Q.toSubgroup.index_ne_zero_of_finite) Q.card_dvd_index).trans hindex
  have hmod := card_sylow_modEq_one 13 H
  have hc : Nat.card (Sylow 13 H)=1 := by
    change Nat.card (Sylow 13 H)%13=1%13 at hmod
    omega
  let : Subsingleton (Sylow 13 H) := (Nat.card_eq_one_iff_unique.mp hc).1
  have hn := Q.normal_of_subsingleton
  exact (normal_subgroupOf_iff_le_normalizer hPH).mp hn
end IndexTwo

end Theory.PSL2.TwentyFive
