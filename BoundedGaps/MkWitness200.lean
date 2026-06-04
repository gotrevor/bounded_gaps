import BoundedGaps.SymmetricReductionOrbitFree
import BoundedGaps.Targets

/-!
# `M_200 > 4` — the first kernel-checked `M_k > 4` in the project

This module instantiates the parts-list-keyed matchings witness
(`Mk_gt_of_symWeight_witness_match_parts`) with the **real** `k = 200`, symmetric-degree `D = 7`
witness: all 45 orbits of `partitions_upto 7`, with the exact-LDL orbit coefficients
(`tools/mk/gen_witness7.py` / `_ldl.py`), giving an exact rational Rayleigh quotient
`≈ 4.002898 > 4`. The three `native_decide`s (Nodup, orbit-disjointness, the rational Gram
quotient) and two `decide`s all run on-box — this needed only a larger interpreter stack
(`weakLeanArgs = ["--tstack=2000000"]` in `lakefile.toml`), NOT a networked host as earlier
handoffs assumed.

`#print axioms Mk_200_gt_4` ⇒ `[propext, Classical.choice, Quot.sound, ofReduceBool
(native_decide)]` — **no mathematical axioms**. The two permanent/rook identities `denom_bridge`
and `num_bridge` (formerly axioms) are now fully kernel-proven theorems (the permanent-route proof
in `SymmetricReductionOrbitFree.lean`); the only non-standard residue is `native_decide` on the
concrete `k = 200` witness computation.
-/

set_option linter.style.longLine false

namespace BoundedGaps.OrbitFree

open scoped Nat

/-- The exact `k=200`, `D=7` witness: all 45 orbits of `partitions_upto 7` with their LDL orbit
coefficients (`tools/mk/gen_witness7.py`). Rational Rayleigh quotient `≈ 4.002898 > 4`. -/
def witnessLCs200 : List (List ℕ × ℚ) :=
[
  ([], (-16606173783052074458560457454268930169432165045092722185513379566407087028370244272867997501830380971029076700 : ℚ)),
  ([1], (119121034113904089800145065160542844045406877591900168738018824144890387734197390396830195372815199207284485939 : ℚ)),
  ([2], (-398487613347069729706680303180616604082848887354678447797820427447992043939485867260723451631538876215432975877 : ℚ)),
  ([1, 1], (-731738894184698562234203733729931579390842705775330250488968084064715150975531819600689160566284992520615627180 : ℚ)),
  ([3], (760722593538272537276655259437880011102218223515494956540879364605148810582722064904624647138375551859607215125 : ℚ)),
  ([2, 1], (2038115968548432836608561769981452648327210697988029771142048749854414674686680530931660966433818329660570925380 : ℚ)),
  ([1, 1, 1], (3742320987239825080652728056388387488177718265471173914765392027284221014302064617963544065908559879028863525310 : ℚ)),
  ([4], (-880445633283954584037800299026126135284278910297880628275604094193812898849538091626338932964731424289096283625 : ℚ)),
  ([3, 1], (-3110208898809655870538729538209953300428926386978330355476924635106524928938829283584613875390866195407380886520 : ℚ)),
  ([2, 2], (-4531313007368283853741084766323564248337158740799719228914982286033688558174003901718244202212104252851274702900 : ℚ)),
  ([2, 1, 1], (-8331833567090122680553543532615373250017182806159833757279671810347987139094078563995526732424862751640195944580 : ℚ)),
  ([1, 1, 1, 1], (-15297377805851802535231730330355656481280286931197654775378730121743306360882139519850311556950958332468253418240 : ℚ)),
  ([5], (614479134141129013239745840422696603846913499675345218191862507208624098542169171364494935714313103656104986007 : ℚ)),
  ([4, 1], (2697737129930942175626287794851664092538397815399744179823349572423818609502187018119161425532636660616087636930 : ℚ)),
  ([3, 2], (5174073757155422880602464035535814935773094196155948640625361424249619454092954705386441210567276795854103791380 : ℚ)),
  ([3, 1, 1], (9528656717447007286877976176562349521827740920213688285969161523438002089354509571965970608960706857078613134660 : ℚ)),
  ([2, 2, 1], (13881718796520238889388039869267123391368479917206486859545253665828577370632731569125047499673609909821466338990 : ℚ)),
  ([2, 1, 1, 1], (25522526855218760386312149619311843301108873479902386940111195026648700794249399598297943431290160689837693539840 : ℚ)),
  ([1, 1, 1, 1, 1], (46855186064346405652987077603445460868213592853118113974311103365228891418161872206900999261175510956333675182600 : ℚ)),
  ([6], (-238713635940110990680449656688760835299920810164499389415258424198184396307825880560714215632160866761650066769 : ℚ)),
  ([5, 1], (-1254302560322540080149639532937692246871839900361899033000928123188506299576994027241069478173911660212166747060 : ℚ)),
  ([4, 2], (-2984769398283860878068424026262971514794298055599741669224687952001366348007129459594246772367862778088916082050 : ℚ)),
  ([4, 1, 1], (-5505962192266078197776616971811989632509712498319245731698432526290336196312925113725034997030104161342361779250 : ℚ)),
  ([3, 3], (-3928608055816006914432326616995651860473769948006449355728885080869868290961367551890374118797419659850350587000 : ℚ)),
  ([3, 2, 1], (-10559413419693563661599361045216527253531647052355886951767624994068776024515248451575967277200588213283398200260 : ℚ)),
  ([3, 1, 1, 1], (-19444756514877815329848279981842231504070797926593141977526184527346827138502056379110238900057677706435182513600 : ℚ)),
  ([2, 2, 2], (-15385795448063442994869227508018500925117867091333498148023042146495798589494078423070062364405103444209487256270 : ℚ)),
  ([2, 2, 1, 1], (-28326312606283154231869303121719791355674480818797153706580600687491299184603541137536039850579834007908772371040 : ℚ)),
  ([2, 1, 1, 1, 1], (-52074831071958056843616708996554755502711836250709764451443662446785741573909595467416815643497768629984259682440 : ℚ)),
  ([1, 1, 1, 1, 1, 1], (-95590046163374512387543377497499831549658007332185197296425657621294770656545438586569726619684433429285462702880 : ℚ)),
  ([7], (39782996248207429991709375397207697932708989627442090343073584292689467205960078868157140576951132199770485982 : ℚ)),
  ([6, 1], (243465389970843705905768061794675130487820341321575028356584270335034805011101438613475934077161013337798347225 : ℚ)),
  ([5, 2], (692319983429993351624716681464359030869562458633897101839977100489086999177895620672243272363958816506235689027 : ℚ)),
  ([5, 1, 1], (1279101436554208274723695337454869056479568567020687527010299846048759037070136391507238913026945227389271319330 : ℚ)),
  ([4, 3], (1130211771859851248118550101516134734535043660141848451665988496913380396520276658893445486530699225936595947625 : ℚ)),
  ([4, 2, 1], (3043540674757178187725660222890462883608513345293328759189014068328193167048222395838566453355147544205338439925 : ℚ)),
  ([4, 1, 1, 1], (5613928312018847869285103016945984464270027447715047018081833452617933260282505739783156711466669659564693139800 : ℚ)),
  ([3, 3, 1], (4005939422215090617382580861333092182399970830489136136008813105299082942404495514333202949411586697322889206060 : ℚ)),
  ([3, 2, 2], (5838761208424240862673823246542158814417959713371245871219885233455120763702255132603285010732182159286032131010 : ℚ)),
  ([3, 2, 1, 1], (10765775220105763233145372109591825154773224618001221688309323510516768756862347267911355397997152465292525851840 : ℚ)),
  ([3, 1, 1, 1, 1], (19822819954640362697560433385869342751971227344612520855345987722100506744656803808285199444055215838757317340280 : ℚ)),
  ([2, 2, 2, 1], (15685565089619757320613425874505031758348633782846370715644515988495712103538042802898638176314710616533361724800 : ℚ)),
  ([2, 2, 1, 1, 1], (28875390505182526777287878148688125409548548215434295799112344515590965630973256716585425548278285899311180881300 : ℚ)),
  ([2, 1, 1, 1, 1, 1], (53078234239501180424691056250267802015375186118862424332770598153374541875905498678097481401974971123095000100240 : ℚ)),
  ([1, 1, 1, 1, 1, 1, 1], (97419335654675309860287287490275446441118368692494806436775276921214601417746179754721334397511695879026242684400 : ℚ))
]

/-- **First kernel-checked `M_k > 4`: `(4:ℝ) < Mk 200`** via the k=200 D=7 matchings witness.
Rests on `[3 std, denom_bridge, num_bridge]` (the two numerically-validated bridge axioms). -/
theorem Mk_200_gt_4 : (4 : ℝ) < Sieve.Mk 200 := by
  have h := Mk_gt_of_symWeight_witness_match_parts (n := 199)
    witnessLCs200
    (by decide) (by decide) (by native_decide)
    (disjoint_of_histogram _ (by native_decide)) 4 (by native_decide)
  exact_mod_cast h

/-! ## A concrete narrow admissible 200-tuple (for a numeric bounded-gap diameter)

`bounded_gap_of_Mk_200` only needs *some* admissible 200-tuple. The cheap existence proof
(`exists_admissible_of_length`) supplies the factorial-spaced tuple of diameter `199·200!` — a
~375-digit number. Here we replace it with an explicit admissible 200-tuple of diameter **1304**
(an upper bound on the narrowness `H(200)`), found by a greedy residue-class sieve over `[0, M)`
removing one minimal-occupancy class per prime `p ≤ 200`, then taking the narrowest 200-survivor
window and normalising to start at `0` (admissibility re-verified after the shift). This turns the
bounded-gap conclusion into a *concrete* numeric bound `liminfGap 1 ≤ 1304`. -/

/-- An explicit admissible 200-tuple of diameter 1304. See the section docstring for provenance. -/
def tuple200 : List ℕ :=
  [0, 8, 12, 24, 30, 32, 38, 44, 54, 60, 68, 72, 78, 80, 84, 92, 102, 110, 120, 122, 128, 134, 144, 150, 158, 164, 168, 180, 182, 192, 194, 198, 200, 210, 212, 222, 224, 228, 242, 248, 252, 254, 260, 264, 270, 278, 288, 290, 294, 302, 312, 318, 320, 332, 338, 344, 348, 354, 368, 374, 378, 380, 390, 392, 402, 404, 408, 414, 420, 422, 428, 434, 450, 452, 462, 470, 480, 492, 494, 498, 500, 518, 522, 530, 540, 554, 558, 560, 564, 578, 582, 584, 590, 600, 612, 618, 624, 630, 632, 638, 642, 644, 654, 660, 662, 674, 684, 704, 708, 710, 714, 722, 728, 732, 738, 744, 752, 758, 764, 770, 774, 782, 788, 798, 800, 810, 822, 824, 830, 840, 848, 864, 870, 872, 882, 884, 890, 908, 914, 918, 938, 942, 948, 950, 960, 962, 974, 978, 980, 990, 992, 998, 1002, 1004, 1008, 1020, 1034, 1038, 1052, 1058, 1064, 1068, 1074, 1080, 1092, 1094, 1100, 1104, 1110, 1118, 1122, 1128, 1130, 1134, 1148, 1152, 1160, 1172, 1178, 1184, 1188, 1190, 1194, 1202, 1212, 1214, 1220, 1232, 1242, 1248, 1250, 1254, 1262, 1268, 1278, 1284, 1290, 1298, 1302, 1304]

theorem tuple200_length : tuple200.length = 200 := by native_decide

theorem tuple200_sorted : tuple200.Pairwise (· < ·) := by native_decide

theorem tuple200_diameter : BoundedGaps.diameter tuple200 = 1304 := by native_decide

/-- Bool-level admissibility checker (mirrors `Engelsma.checkAdm`): `true` iff some residue
`r ∈ {0,…,p-1}` is missed by every element of `tuple200` mod `p`. -/
private def checkAdm200 (p : ℕ) : Bool :=
  (List.range p).any fun r => tuple200.all fun h => !(h % p == r)

/-- Every prime `≤ 200` passes the admissibility check, by one bundled `native_decide` (46 primes). -/
private lemma admCheck200_true :
    ((List.range 201).filter Nat.Prime).all (fun p => checkAdm200 p) = true := by native_decide

/-- Extract a concrete `Nat`-level missed residue `r < p` from the Bool check passing at `p`. -/
private lemma admCheck200_implies (p : ℕ) (hp : p.Prime) (hle : p ≤ 200) :
    ∃ r : ℕ, r < p ∧ ∀ h ∈ tuple200, h % p ≠ r := by
  have hmem : p ∈ (List.range 201).filter Nat.Prime := by
    rw [List.mem_filter]; exact ⟨List.mem_range.mpr (by omega), by simp [hp]⟩
  have hpass := List.all_eq_true.mp admCheck200_true p hmem
  obtain ⟨r, hr_mem, hr_all⟩ := List.any_eq_true.mp hpass
  refine ⟨r, List.mem_range.mp hr_mem, fun h hh habs => ?_⟩
  have := List.all_eq_true.mp hr_all h hh
  simp [beq_eq_false_iff_ne] at this
  exact this habs

/-- The finite-prime admissibility check for `tuple200`, in `ZMod p` form — the obligation
`admissible_of_check_small_primes` consumes. -/
theorem tuple200_check :
    ∀ p : ℕ, p.Prime → p ≤ 200 → ∃ r : ZMod p, ∀ h ∈ tuple200, (h : ZMod p) ≠ r := by
  intro p hp hle
  obtain ⟨r, hr_lt, hr_mod⟩ := admCheck200_implies p hp hle
  refine ⟨(r : ZMod p), fun h hh habs => ?_⟩
  have hne := hr_mod h hh
  rw [ZMod.natCast_eq_natCast_iff'] at habs
  rw [Nat.mod_eq_of_lt hr_lt] at habs
  exact hne habs

/-- `tuple200` is admissible: strictly sorted (`native_decide`), and for every prime `p ≤ 200` it
misses a residue class (bundled `native_decide`); primes `p > 200` are closed by pigeonhole
(`admissible_of_check_small_primes`, since `|tuple200| = 200 < p`). -/
theorem tuple200_admissible : BoundedGaps.Admissible tuple200 :=
  BoundedGaps.admissible_of_check_small_primes tuple200_sorted
    (fun p hp hple => tuple200_check p hp (tuple200_length ▸ hple))

/-- **`H(200) ≤ 1304`.** `tuple200` witnesses an upper bound on the narrowness
(minimal admissible-tuple diameter) at `k = 200`. -/
theorem narrowness_200_le_1304 : BoundedGaps.narrowness 200 ≤ 1304 :=
  BoundedGaps.narrowness_le_of_admissible_tuple tuple200_admissible tuple200_length
    tuple200_diameter

/-- **Unconditional bounded gaps from `M_200 > 4`.** Feeding the kernel-checked `Mk_200_gt_4`
into the Maynard–Bombieri–Vinogradov bridge `Targets.H1_le_of_Mk_witness`: there is an admissible
200-tuple `H` whose diameter bounds `liminfGap 1` (a finite bound on the prime gap that recurs
infinitely often). Unlike `Targets.H1_le_246` — which is *conditional* on the unproven
`Mk 50 > 4` — this rests only on the standard analytic-NT inputs (`BombieriVinogradov` etc.); the
`Mk 200 > 4` input itself is now axiom-clean. The witness tuple is the explicit narrow `tuple200`
(diameter 1304), so the conclusion is a *concrete* numeric bound (see `liminfGap_one_le_1304`), not
merely the astronomical factorial-spaced tuple's; the content is that `Mk 200 > 4`
*unconditionally* forces bounded gaps. -/
theorem bounded_gap_of_Mk_200 :
    ∃ H : List ℕ, BoundedGaps.Admissible H ∧ H.length = 200 ∧
      BoundedGaps.liminfGap 1 ≤ (BoundedGaps.diameter H : ℕ∞) :=
  ⟨tuple200, tuple200_admissible, tuple200_length,
    BoundedGaps.Targets.H1_le_of_Mk_witness 200 tuple200 tuple200_admissible tuple200_length
      Mk_200_gt_4⟩

/-- **The concrete numeric bounded-gap bound.** The smallest prime gap that recurs infinitely
often, `liminfGap 1 = H_1`, is at most **1304** — the diameter of the explicit admissible 200-tuple
`tuple200`. This is the numeric payoff of `bounded_gap_of_Mk_200`: `Mk 200 > 4` (axiom-clean) plus
the standard analytic-NT inputs force infinitely many prime pairs within a window of length 1304. -/
theorem liminfGap_one_le_1304 : BoundedGaps.liminfGap 1 ≤ (1304 : ℕ∞) := by
  have h := BoundedGaps.Targets.H1_le_of_Mk_witness 200 tuple200 tuple200_admissible
    tuple200_length Mk_200_gt_4
  rw [tuple200_diameter] at h
  exact_mod_cast h

/-- **Bounded gaps between primes exist (unconditionally, mod the disclosed axioms).** The sharpest
qualitative form: `H_1 = liminf_n (p_{n+1} - p_n)` is *finite*. Immediate from `bounded_gap_of_Mk_200`
(`liminfGap 1` is bounded by a concrete finite diameter). -/
theorem liminfGap_one_lt_top : BoundedGaps.liminfGap 1 < ⊤ := by
  obtain ⟨H, _, _, hle⟩ := bounded_gap_of_Mk_200
  exact lt_of_le_of_lt hle (ENat.coe_lt_top _)

end BoundedGaps.OrbitFree

#print axioms BoundedGaps.OrbitFree.Mk_200_gt_4
#print axioms BoundedGaps.OrbitFree.bounded_gap_of_Mk_200
#print axioms BoundedGaps.OrbitFree.liminfGap_one_le_1304
