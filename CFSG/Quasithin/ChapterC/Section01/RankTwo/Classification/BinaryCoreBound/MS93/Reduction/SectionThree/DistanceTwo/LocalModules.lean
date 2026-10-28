module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Classification
public import Theory.Frattini.OmegaProducts

/-!
# Binary module extraction at critical distance two

The positive-distance module classification identifies [X_alpha,Ltilde_alpha]
with U_alpha. To extract a natural U in the non-Frattini branch, we prove the
commutator noncontainment displayed in the first paragraph of MS93 (3.6).

Work inside the actual finite stabilizer G_alpha. If a critical Z_c centralizes
Q_alpha modulo Phi(Q_alpha)X_alpha, the kernel of that action is normal and
contains Q_alpha. Critical reversal says Z_c is not contained in Q_alpha.
Simplicity of the specified SL3(2) quotient therefore makes the whole stabilizer
centralize this section, contradicting the non-Frattini premise.

At distance two, Q_alpha lies in the midpoint kernel and centralizes
[Z_alpha,Z_c]. Thus the proved binary bad-case bound from (3.3) contradicts the
commutator noncontainment. The doubled and nonsplit alternatives are retained
until this step. All groups, actions, relative normality and critical pairs are
the source ones; no natural structure or abelianness of the core is assumed.
The simple-quotient argument proves the needed implication directly, without
invoking the general characteristic replacement of (3.4).

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.2)--(3.3), printed pp.863--868, and (3.6), first paragraph, p.870.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo

/-- A nontrivial kernel element in the simple quotient forces trivial action
on the abelian image of P in G/N. -/
private theorem simple_quotient_commutator
    {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]
    (π : G →* S) (hπ : Function.Surjective π)
    (P N E : Subgroup G) [P.Normal] [N.Normal]
    (hker : π.ker = P) (hPP : ⁅P,P⁆ ≤ N)
    (hE : ¬ E ≤ P) (hPE : ⁅P,E⁆ ≤ N) : ⁅P,⊤⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  let C := (centralizer (P.map q : Set (G ⧸ N))).comap q
  have hC (A : Subgroup G) : A ≤ C ↔ ⁅P,A⁆ ≤ N := by
    change A ≤ (centralizer (P.map q : Set (G ⧸ N))).comap q ↔ _
    rw [← map_le_iff_le_comap, ← le_centralizer_iff,
      ← commutator_eq_bot_iff_le_centralizer, ← map_commutator,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hPC : P ≤ C := (hC P).mpr hPP
  have hEC : E ≤ C := (hC E).mpr hPE
  let : (P.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  have htop : C.map π = ⊤ := by
    apply (Normal.map (inferInstance : C.Normal) π hπ).eq_bot_or_eq_top.resolve_left
    intro hz
    have hCK : C ≤ π.ker := (map_eq_bot_iff C).mp hz
    exact hE (hEC.trans (hker ▸ hCK))
  have hCt : C = ⊤ := by
    have h := congrArg (Subgroup.comap π) htop
    rw [comap_map_eq, comap_top, hker, sup_of_le_left hPC] at h
    exact h
  exact (hC ⊤).mp (by rw [hCt])

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The (3.2) commutator identity needed in the Frattini-small branch of (3.6). -/
theorem X_commutator_eq_U (source : LocalSource L R) (geometry : Geometry R)
    (hb : geometry.b R = 2) :
    ⁅X R (alpha R), Ltilde R (alpha R)⁆ = U R (alpha R) :=
  ModuleAlternatives.X_commutator_eq_U source geometry (by omega)

omit [Finite M] in
private theorem local_frattini_map (P S : Subgroup (FreeAmalgam R)) (hPS : P ≤ S) :
    ((frattini (P.subgroupOf S)).map (P.subgroupOf S).subtype).map S.subtype =
      (frattini P).map P.subtype := by
  let e := subgroupOfEquivOfLe hPS
  calc
    _ = ((frattini (P.subgroupOf S)).map e.toMonoidHom).map P.subtype := by
      rw [map_map, map_map]
      rfl
    _ = _ := by rw [frattini_map_equiv]

/-- A critical endpoint detects the action on the Frattini section of Q. -/
private theorem core_le_of_critical_commutator_le
    (source : LocalSource L R) (geometry : Geometry R) (hb : 0 < geometry.b R)
    (c : Vertex R) (hc : CriticalPair R (alpha R) c
      (geometry.exists_critical (alpha R) rfl))
    (hcomm : ⁅Q R (alpha R), Z R c⁆ ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R) := by
  let S := stabilizer R (alpha R)
  let P := (Q R (alpha R)).subgroupOf S
  let W := (X R (alpha R)).subgroupOf S
  let N := (frattini P).map P.subtype ⊔ W
  let E := (Z R c).subgroupOf S
  let : Finite S := finite_stabilizer R (alpha R)
  let : P.Normal := Q_normal R (alpha R)
  let : W.Normal := X_normal R (alpha R)
  let : ((frattini P).map P.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : Fact (IsPGroup 2 P) :=
    ⟨(Q_isPGroup R source.two_group source.core_le (alpha R) rfl).comap_subtype⟩
  have hP : Q R (alpha R) ≤ S := fun _ hx => hx.1
  have hW : X R (alpha R) ≤ S := (omegaCenter_le _).trans hP
  have hPm : P.map S.subtype = Q R (alpha R) := map_subgroupOf_eq_of_le hP
  have hWm : W.map S.subtype = X R (alpha R) := map_subgroupOf_eq_of_le hW
  have hNm : N.map S.subtype =
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R) := by
    rw [Subgroup.map_sup, hWm, local_frattini_map _ _ hP]
  have hcc := critical_endpoint_color R (alpha R) rfl _ hc
  have hrev := MS93.critical_reverse R geometry (source.edgeCentralizerCondition geometry)
    (alpha R) rfl hb c hcc hc
  have hZ : Z R c ≤ S :=
    (geometry.omega_bound c hcc (by rw [geometry.distance_constant c hcc]; exact hb)).trans
      (critical_X_le_stabilizer source geometry hb c hcc (alpha R) hrev)
  have hEm : E.map S.subtype = Z R c := map_subgroupOf_eq_of_le hZ
  have hPP : ⁅P,P⁆ ≤ N := by
    apply le_trans _ le_sup_left
    rw [← map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hE : ¬ E ≤ P := by
    intro he
    exact hrev.2 (by simpa only [hEm, hPm] using map_mono (f := S.subtype) he)
  have hPE : ⁅P,E⁆ ≤ N := by
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    simpa only [map_commutator, hPm, hEm, hNm] using hcomm
  have hh := simple_quotient_commutator (baseProjection source)
    (baseProjection_surjective source) P N E (baseProjection_kernel source) hPP hE hPE
  have hm := map_mono (f := S.subtype) hh
  rw [map_commutator, hPm, hNm] at hm
  exact (commutator_mono le_rfl (show Ltilde R (alpha R) ≤ (⊤ : Subgroup S).map S.subtype from
    map_mono le_top)).trans hm

/-- The displayed noncontainment in the first paragraph of source (3.6).
It follows from the non-Frattini premise for every genuine critical pair. -/
theorem critical_commutator_not_le
    (source : LocalSource L R) (geometry : Geometry R) (hb : 0 < geometry.b R)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    (c : Vertex R) (hc : CriticalPair R (alpha R) c
      (geometry.exists_critical (alpha R) rfl)) :
    ¬ ⁅Q R (alpha R), Z R c⁆ ≤
      ⁅Q R (alpha R), X R c ⊓ Q R (alpha R)⁆ ⊔ ⁅X R (alpha R), X R c⁆ := by
  intro h
  apply hlarge
  apply core_le_of_critical_commutator_le source geometry hb c hc
  apply h.trans
  apply sup_le
  · apply le_trans (commutator_mono le_rfl inf_le_right)
    apply le_trans _ le_sup_left
    let := finite_stabilizer R (alpha R)
    let : Finite (Q R (alpha R)) := Finite.of_injective
      (inclusion (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1))
      (inclusion_injective _)
    let : Fact (IsPGroup 2 (Q R (alpha R))) :=
      ⟨Q_isPGroup R source.two_group source.core_le (alpha R) rfl⟩
    rw [← map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  · exact ((critical_commutator_le_intersection source geometry hb
      (alpha R) rfl c hc).trans inf_le_left).trans le_sup_right

/-- In the non-Frattini distance-two branch the literal moving layer U
is natural for the specified SL3(2) quotient, with an actual equivariant map. -/
theorem naturalU_of_not_le_frattini_sup
    (source : LocalSource L R) (geometry : Geometry R) (hb : geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    Nonempty (NaturalU R source.projection) := by
  have hbpos : 0 < geometry.b R := by omega
  rcases ModuleAlternatives.alternatives source geometry hbpos with hnatural | hbad
  · exact hnatural.1
  · exfalso
    obtain ⟨c, hc⟩ := criticalPair_exists R (alpha R) (geometry.exists_critical (alpha R) rfl)
    have hd : (cosetGraph R).dist (alpha R) c = 2 := hc.1.trans hb
    obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two R (alpha R) c hd
    have hcol : color R t = true := by
      have hn := adjacent_color_ne R hat
      change false ≠ color R t at hn
      cases ht : color R t <;> simp_all
    have hdt : (cosetGraph R).dist (alpha R) t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
    have hcc := critical_endpoint_color R (alpha R) rfl _ hc
    have hZa : Z R (alpha R) ≤ X R (alpha R) := geometry.omega_bound (alpha R) rfl hbpos
    have hZc : Z R c ≤ X R c := geometry.omega_bound c hcc
      (by rw [geometry.distance_constant c hcc]; exact hbpos)
    have hR : ⁅Z R (alpha R), Z R c⁆ ≤ X R (alpha R) :=
      (commutator_mono hZa hZc).trans
        ((critical_commutator_le_intersection source geometry hbpos (alpha R) rfl c hc).trans
          inf_le_left)
    have hactor : Q R (alpha R) ≤ Q R t ⊓
        centralizer ((⁅Z R (alpha R), Z R c⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
      le_inf (Q_le_adjacent_h R hcol hat)
        ((Q_le_centralizer_X R (alpha R)).trans (centralizer_le hR))
    have hbound := ModuleAlternatives.badCase_source33Bound source geometry hbpos hbad
      (alpha R) rfl c hc t hct (by omega) (Q R (alpha R)) hactor
    have hzero : ⁅X R (alpha R) ⊓ Q R c, Q R (alpha R)⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (inf_le_left.trans (le_centralizer_iff.mp (Q_le_centralizer_X R (alpha R))))
    rw [hzero, sup_bot_eq, commutator_comm] at hbound
    exact critical_commutator_not_le source geometry hbpos hlarge c hc
      (hbound.trans le_sup_right)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo
