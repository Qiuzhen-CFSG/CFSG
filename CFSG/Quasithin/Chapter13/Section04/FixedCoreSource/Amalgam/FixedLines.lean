module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ResidualKernel
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.OmegaLine
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.ThompsonNormalizer
public import Theory.GroupTheory.ConjugationLocalGeometry
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The two fixed lines of an applicable original pair

The common Sylow supplement shows C_Z(Hᵢ)=C_Z(O²(Hᵢ)). If these two
fixed subgroups coincide, the residual identity in 13.4.7(c) puts one
local residual in the other. Their S₃ quotients and common Sylow then
force H₁=H₂, a contradiction.

For an escaping vertex, its fixed subgroup intersects C_Z(L) trivially:
a nonidentity element of this intersection would put the vertex in M by
maximal two-local uniqueness. Both subgroups have index two in Z, so
|Z|≤4. The original fixed line and |Z:C_Z(L)|=2 give equality. Thus the
two distinct fixed subgroups have order two and split Z as a direct
product; C_Z(L) is the original line C_V(L).

Source: Aschbacher–Smith 13.4.7, printed p.900. Escape from M and the
preceding 13.4.3 index are explicit inputs; the original-pair consumer
constructs the former. No structural alternative is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The vertex and its two-residual fix the same part of the common Sylow center. -/
theorem omega_fixed_twoResidual {T : Sylow 2 G} (A : Subgroup G)
    (hTA : (T : Subgroup G) ≤ A) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓
        centralizer ((pResidual 2 A).map A.subtype : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G) := by
  have hgen : (pResidual 2 A).map A.subtype ⊔ (T : Subgroup G) = A := by
    have hm := congrArg (map A.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTA))
    rwa [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTA,
      ← MonoidHom.range_eq_map,range_subtype] at hm
  apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le (map_subtype_le _)))
  intro z hz
  refine ⟨hz.1,?_⟩
  have ha : A ≤ centralizer ({z} : Set G) := by
    rw [←hgen]
    refine sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (hz.2 a ha)) ?_
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2 t ht)
  exact fun a h => mem_centralizer_singleton_iff.mp (ha h)

/-- The prime-to-three identity in (c) prevents the two fixed subgroups from coinciding. -/
theorem pair_fixed_subgroups_ne {T : Sylow 2 G} {A B : Subgroup G}
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G) ≠
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have step (P Q : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
      (hTQ : (T : Subgroup G) ≤ Q)
      (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
      (eQ : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3))
      (hPQ : P ≠ Q) (hQX : Q ≤ X)
      (hr : let K := (pResidual 2 P).map P.subtype
        let C := X ⊓ centralizer ((Z ⊓ centralizer (K : Set G) : Subgroup G) : Set G)
        (primeToResidual 3 C).map C.subtype = K)
      (hf : Z ⊓ centralizer (P : Set G) = Z ⊓ centralizer (Q : Set G)) : False := by
    let C := X ⊓ centralizer ((Z ⊓ centralizer (Q : Set G) : Subgroup G) : Set G)
    have hQC : Q ≤ C := le_inf hQX (le_centralizer_iff.mpr inf_le_right)
    have hr' : (primeToResidual 3 C).map C.subtype = (pResidual 2 P).map P.subtype := by
      have hfix := omega_fixed_twoResidual P hTP
      change Z ⊓ centralizer ((pResidual 2 P).map P.subtype : Set G) =
        Z ⊓ centralizer (P : Set G) at hfix
      dsimp only at hr
      rw [hfix,hf] at hr
      exact hr
    have hKQ : (pResidual 2 Q).map Q.subtype ≤ (pResidual 2 P).map P.subtype := by
      rw [SymmetricThreeTwoCore.twoResidual_eq_primeToThree eQ,←hr']
      exact embedded_primeToResidual_mono 3 hQC
    have hQP : Q ≤ P := by
      have hm := congrArg (map Q.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTQ))
      rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTQ,
        ← MonoidHom.range_eq_map,range_subtype] at hm
      rw [←hm]
      exact sup_le (hKQ.trans (map_subtype_le _)) hTP
    have hQT : Q = (T : Subgroup G) := by
      simpa only [inf_eq_right.mpr hQP] using intersection_eq_sylow hTP hTQ eP eQ hPQ
    have hi := SymmetricThreeTwoCore.sylow_index_three eQ (T.subtype hTQ)
    change (T : Subgroup G).relIndex Q = 3 at hi
    rw [←hQT,relIndex_self] at hi
    omega
  intro hf
  rcases hres with hr | hr
  · exact step A B hTA hTB eA eB hne le_sup_right hr hf
  · exact step B A hTB hTA eB eA hne.symm le_sup_left hr hf.symm

/-- The source hyperplane argument for any escaping pair, with its literal two fixed lines. -/
theorem original_pair_fixed_lines {T : Sylow 2 G} {L V A B : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (L : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hdistinct : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G) ≠
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let F₁ := Z ⊓ centralizer (A : Set G)
    let F₂ := Z ⊓ centralizer (B : Set G)
    Nat.card Z = 4 ∧ Nat.card F₁ = 2 ∧ Nat.card F₂ = 2 ∧
      F₁ ⊓ F₂ = ⊥ ∧ F₁ ⊔ F₂ = Z ∧
      Z ⊓ centralizer (L : Set G) = V ⊓ centralizer (L : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F := Z ⊓ centralizer (L : Set G)
  let F₁ := Z ⊓ centralizer (A : Set G)
  let F₂ := Z ⊓ centralizer (B : Set G)
  have hbound (Y : Subgroup G) (hy : ¬ Y ≤ normalizer (L : Set G))
      (hi : (Z ⊓ centralizer (Y : Set G)).relIndex Z = 2) : Nat.card Z ≤ 4 := by
    have hz : F ⊓ (Z ⊓ centralizer (Y : Set G)) = ⊥ := by
      apply eq_bot_iff.mpr
      intro d hd
      by_contra hd1
      apply hy
      apply le_trans ?_ (Solvable.omega_fixed_generator_centralizer_le_normalizer
        h structural hd.1.1 hd.1.2 hd1)
      exact fun y hy => mem_centralizer_singleton_iff.mpr (hd.2.2 y hy)
    have hb := relIndex_inf_le (H := F) (K := Z ⊓ centralizer (Y : Set G)) (L := Z)
    rwa [hz,relIndex_bot_left,hindexL,hi] at hb
  have hc : Nat.card Z ≤ 4 := by
    by_cases hA : A ≤ normalizer (L : Set G)
    · exact hbound B (fun hB => hout (sup_le hA hB)) hindexB
    · exact hbound A hA hindexA
  have hfix : V ⊓ centralizer (L : Set G) ≤ F :=
    le_inf (Solvable.fixed_le_original_omegaCenter h structural D m) inf_le_right
  have hlow := card_le_of_le hfix
  rw [m.card_fixed] at hlow
  have hcount (Y : Subgroup G) :
      Nat.card (Z ⊓ centralizer (Y : Set G) : Subgroup G) *
        (Z ⊓ centralizer (Y : Set G)).relIndex Z = Nat.card Z := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G)
      (Z ⊓ centralizer (Y : Set G)) Z bot_le inf_le_left
    simpa only [relIndex_bot_left] using hh
  have hL := hcount L
  rw [hindexL] at hL
  change Nat.card F * 2 = Nat.card Z at hL
  have hZ : Nat.card Z = 4 := by change 2 ≤ Nat.card F at hlow; nlinarith
  have hFA := hcount A
  have hFB := hcount B
  rw [hindexA,hZ] at hFA
  rw [hindexB,hZ] at hFB
  change Nat.card F₁ * 2 = 4 at hFA
  change Nat.card F₂ * 2 = 4 at hFB
  have hF₁ : Nat.card F₁ = 2 := by omega
  have hF₂ : Nat.card F₂ = 2 := by omega
  have hinf : F₁ ⊓ F₂ = ⊥ := inf_eq_bot_of_card_two_of_ne F₁ F₂ hF₁ hF₂ hdistinct
  have hn : F₂ ≤ normalizer (F₁ : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb a ha
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hb.1).2.2 a
      ((mem_omegaOneCenterAmbient_iff _ _).mp ha.1).1
  have hs : F₁ ⊔ F₂ = Z := by
    apply eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint F₁ F₂ hn (disjoint_iff.mpr hinf),hF₁,hF₂,hZ]
  refine ⟨hZ,hF₁,hF₂,hinf,hs,?_⟩
  exact (eq_of_le_of_card_ge hfix (by rw [m.card_fixed]; rw [hZ] at hL; omega)).symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
