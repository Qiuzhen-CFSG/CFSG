module
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SourceLifting
public import Theory.GroupTheory.NormalSymmetricThreeEscape

/-!
# The two parabolics of a symmetric-three pair quotient

A proper strict overgroup of a Sylow two-subgroup in S₃ × S₃ has order
12 and is maximal. The model's two-parabolic classification therefore
identifies any two distinct such overgroups, including their intersection.
Pulling back through a normal two-group kernel preserves the full lattice
statement. A normal S₃ section supplementing one parabolic constructs the
other as its join with the original Sylow subgroup.

This supplies the line residue in Aschbacher–Smith 13.4.9, printed p.906,
from the actual local product in 13.4.8, rather than assuming its geometry.
-/

public noncomputable section
open Subgroup
namespace Quasithin.I5.RankTwoParabolics
variable {G : Type*} [Group G] [Finite G]
private theorem coatom_of_pair_strict (e : G ≃* SymmetricThreeProduct.G)
    (S : Sylow 2 G) (P : Subgroup G) (hSP : (S : Subgroup G) < P)
    (hP : P ≠ ⊤) : IsCoatom P := by
  obtain ⟨R,hR,hPR⟩ := (eq_top_or_exists_le_coatom P).resolve_left hP
  have hp := (SymmetricThreeProduct.intermediate_card_and_core e S P hSP hP).1
  have hr := (SymmetricThreeProduct.intermediate_card_and_core e S R
    (hSP.trans_le hPR) hR.ne_top).1
  exact (eq_of_le_of_card_ge hPR (by rw [hp,hr])).symm ▸ hR

theorem of_pair_model (e : G ≃* SymmetricThreeProduct.G) (S : Sylow 2 G)
    (P R : Subgroup G) (hSP : (S : Subgroup G) < P) (hSR : (S : Subgroup G) < R)
    (hP : P ≠ ⊤) (hR : R ≠ ⊤) (hne : P ≠ R) :
    Quasithin.I5.RankTwoParabolics G (S : Subgroup G) P R := by
  let E := e.mapSubgroup
  obtain ⟨A,B,_,hi,hclass⟩ := SymmetricThreeProduct.exists_parabolics_over_sylow
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hp := coatom_of_pair_strict e S P hSP hP
  have hr := coatom_of_pair_strict e S R hSR hR
  have hc (U : Subgroup G) (hU : IsCoatom U) (hSU : (S : Subgroup G) ≤ U) :
      E U = A ∨ E U = B :=
    (hclass (E U)).mp ⟨(E.isCoatom_iff U).mpr hU,E.monotone hSU⟩
  have hp' := hc P hp hSP.le
  have hr' := hc R hr hSR.le
  have hd : E P ≠ E R := fun he => hne (E.injective he)
  refine ⟨hp,hr,hne,?_,?_⟩
  · apply E.injective
    rw [E.map_inf]
    rcases hp' with hp' | hp' <;> rcases hr' with hr' | hr'
    · exact (hd (hp'.trans hr'.symm)).elim
    · rw [hp',hr']; exact hi
    · rw [hp',hr',inf_comm]; exact hi
    · exact (hd (hp'.trans hr'.symm)).elim
  · intro U hSU hU
    have hu := hc U hU hSU
    rcases hp' with hp' | hp' <;> rcases hr' with hr' | hr'
    · exact (hd (hp'.trans hr'.symm)).elim
    · exact hu.imp (fun hh => E.injective (hh.trans hp'.symm))
        (fun hh => E.injective (hh.trans hr'.symm))
    · exact hu.symm.imp (fun hh => E.injective (hh.trans hp'.symm))
        (fun hh => E.injective (hh.trans hr'.symm))
    · exact (hd (hp'.trans hr'.symm)).elim

theorem of_pair_two_quotient (N : Subgroup G) [N.Normal] (hn : IsPGroup 2 N)
    (e : (G ⧸ N) ≃* SymmetricThreeProduct.G) (S : Sylow 2 G)
    (P R : Subgroup G) (hSP : (S : Subgroup G) < P) (hSR : (S : Subgroup G) < R)
    (hP : P ≠ ⊤) (hR : R ≠ ⊤) (hne : P ≠ R) :
    Quasithin.I5.RankTwoParabolics G (S : Subgroup G) P R := by
  let q := QuotientGroup.mk' N
  have hq := QuotientGroup.mk'_surjective N
  have hk : q.ker ≤ (S : Subgroup G) := by
    rw [QuotientGroup.ker_mk']; exact hn.le_sylow_of_normal S
  have hc (U : Subgroup G) (hSU : (S : Subgroup G) ≤ U) :
      (U.map q).comap q = U := comap_map_eq_self (hk.trans hSU)
  have hs (U : Subgroup G) (hSU : (S : Subgroup G) < U) :
      (S : Subgroup G).map q < U.map q := by
    refine lt_of_le_of_ne (map_mono hSU.le) ?_
    intro he
    have hh := congrArg (comap q) he
    rw [hc _ le_rfl,hc U hSU.le] at hh
    exact hSU.ne hh
  have hp (U : Subgroup G) (hSU : (S : Subgroup G) ≤ U) (hu : U ≠ ⊤) :
      U.map q ≠ ⊤ := by
    intro he
    exact hu (by rw [←hc U hSU,he,comap_top])
  have hd : P.map q ≠ R.map q := by
    intro he
    have hh := congrArg (comap q) he
    rw [hc P hSP.le,hc R hSR.le] at hh
    exact hne hh
  have hh := (of_pair_model e (S.mapSurjective hq) (P.map q) (R.map q)
    (hs P hSP) (hs R hSR) (hp P hSP.le hP) (hp R hSR.le hR) hd).comap_surjective q hq
  change Quasithin.I5.RankTwoParabolics G (((S : Subgroup G).map q).comap q)
    ((P.map q).comap q) ((R.map q).comap q) at hh
  rwa [hc _ le_rfl,hc P hSP.le,hc R hSR.le] at hh

theorem of_normal_symmetricThree_supplement
    (eG : (G ⧸ pCore 2 G) ≃* SymmetricThreeProduct.G)
    (N M : Subgroup G) [N.Normal]
    (eN : (N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 3))
    (eM : (M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 3))
    (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M) (hM : M ≠ ⊤)
    (hgen : N ⊔ M = ⊤) :
    Quasithin.I5.RankTwoParabolics G (S : Subgroup G) M (N ⊔ (S : Subgroup G)) := by
  obtain ⟨hout,hproper,_⟩ := Theory.GroupTheory.normal_symmetricThree_supplement_controls_escape
    eG N M eN eM S hSM hM hgen
  have hMstrict : (S : Subgroup G) < M := by
    apply lt_iff_le_not_ge.mpr
    refine ⟨hSM,?_⟩
    intro hh
    have hp : IsPGroup 2 (Equiv.Perm (Fin 3)) :=
      ((S.isPGroup'.to_le hh).to_quotient (pCore 2 M)).of_equiv eM
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    have hthree : 3 ∣ Nat.card (Equiv.Perm (Fin 3)) := by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
    rw [hn] at hthree
    exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree)
  exact of_pair_two_quotient (pCore 2 G) pCore_isPGroup eG S M _ hMstrict
    (lt_iff_le_not_ge.mpr ⟨le_sup_right,fun hh => hout (hh.trans hSM)⟩)
    hM hproper (fun he => hout he.symm.le)
end Quasithin.I5.RankTwoParabolics
