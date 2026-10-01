# Attribution and source boundary

The submission presents additional formalization and integration for JSP-001006 / Erdős problem 1201. Repository ownership is not used as evidence that the submitter authored every dependency or the underlying mathematical argument.

## Mathematical argument

Przemek Chojecki publicly posted the lower-natural-density argument on 30 April 2026; the unconditional argument is recorded in Theorem 1.1 and §8 of the [1 May 2026 note](https://www.ulam.ai/research/erdos1201-lpd.pdf). The analytic foundation is the work of Kaisa Matomäki and Maksym Radziwiłł; see [*Multiplicative functions in short intervals*, Annals of Mathematics 183 (2016), 1015–1056](https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n3-p06-p.pdf). These mathematical contributions are not claimed by the submitting account.

## Submitted contribution

Submission maintainer: GitHub account [`peilinliu66-dev`](https://github.com/peilinliu66-dev). The submitted contribution consists of the new and bridge modules below, the localized integrations described separately, the version and proof repairs, and reproduction/audit tooling. Development and repair used OpenAI ChatGPT/Codex assistance. This statement does not assign a legal identity from the account name or claim that an automated tool is an independent human verifier.

The additional development and compiler repairs are submitted and maintained by peilinliu66-dev, with ChatGPT/Codex assistance. The exact proof commit is supplied in the award submission. The module boundary below, REPAIR_LEDGER.md and verification/verified-proof-snapshot.json identify the contribution and checked bytes. Repository ownership does not establish sole authorship or first priority.

The following twenty root proof modules are intended to be tracked directly, with existing source notices preserved:

```text
CofactorCounting.lean
ComparisonBudget.lean
DyadicBadWindows.lean
DyadicDensity.lean
Elementary.lean
Erdos1201.lean
FarCofactors.lean
FarEnergyTransfer.lean
FarRecombination.lean
FarSetUtils.lean
LongWindowDeficit.lean
LongWindowUniform.lean
OriginalThreshold.lean
PerronThreeBand.lean
PrimeWindow.lean
RealFarEnergy.lean
RealFarSeparation.lean
RealTwoLengthComparison.lean
ThetaLogPower.lean
TruncationComparison.lean
```

`VerifyOriginalStatement.lean` is a separate submitted verification entry. `Erdos1201.lean` retains attribution to the Formal Conjectures Authors for the copied set definition, with its stated original source revision `e04cc601840dd7a37f89b821a67f3a9e3c38d9c3`. The declaration file retains the source attribution; the applicable Apache-2.0 notice is included in `licenses/FormalConjectures-Apache-2.0.txt`. The later reference used for correspondence review is `137aec5c7abd3aa61f7a73138a97279acfc79e93`; the reference statement file was unchanged across the intervening checked snapshots. A project-wide license for newly contributed material must not override that notice or the licenses of downloaded dependencies.

## Downloaded and generated proof inputs

The build depends on 589 selected source modules from [`plby/lean-proofs` at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest), together with 183 selected BoundedGaps source modules from [`frenzymath/FormalPantheon` at `ffbb65c21afc8a36ace67720f1b0df1c63d26bd1`](https://github.com/frenzymath/FormalPantheon/tree/ffbb65c21afc8a36ace67720f1b0df1c63d26bd1/BoundedGaps). Existing source authorship belongs to those contributors; it is not transferred to this submitter. mathlib and its dependencies retain their own attribution and licenses.

The eleven localized files below are adapted from the named plby sources under `src/latest/ErdosProblems/Erdos67b/` at that exact commit. Their accepted headers already identify the source. Under this public boundary, they are generated locally, ignored by Git and excluded from public source archives. The generator must obtain the pinned upstream source and apply described local transformations; embedding an entire derived file as a string or encoded blob would reintroduce that source into the public repository.

| Generated local file | Upstream source file |
| --- | --- |
| `FarAmbient.lean` | `MRCofactorSelectedAmbient.lean` |
| `FarCutoffPayment.lean` | `MRCofactorSelectedCutoffPayment.lean` |
| `FarExceptionalEnergy.lean` | `MRFixedPowerExceptionalEnergy.lean` |
| `FarLargePrimeEnergy.lean` | `MRSelectedLargePrimeEnergy.lean` |
| `FarNoSmallEnergy.lean` | `MRSelectedNoSmallEnergy.lean` |
| `FarPaidProduct.lean` | `MRCofactorSelectedPaidProduct.lean` |
| `FarRectangle.lean` | `MRCofactorSelectedScheduledRectangle.lean` |
| `FarSampleEnergy.lean` | `MRSelectedPaidSampleEnergy.lean` |
| `FarSampleSmall.lean` | `MRSelectedPaidSampleSmall.lean` |
| `FarScheduledEnergy.lean` | `MRScheduledSmallEnergy.lean` |
| `FarTypicalEnergy.lean` | `MRFixedPowerTypicalEnergy.lean` |

The principal mathematical adaptation restricts cancellation to frequencies whose whole local window avoids zero. The submitted integration must identify these adaptations as derived work, even when the full resulting files are generated rather than committed.

## License facts and remaining question

No blanket redistribution permission covering the selected plby closure or these eleven derived modules has been confirmed. The upstream [`src/latest/LICENSE`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/LICENSE) identifies only some files as external Apache-2.0 contributions. It must not be read as a license for all 589 selected files. The public-source download procedure is a reproduction mechanism, not a permission grant or a statement that every downstream use has been cleared.

The BoundedGaps source is covered by the applicable [FormalPantheon Apache-2.0 license](https://github.com/frenzymath/FormalPantheon/blob/ffbb65c21afc8a36ace67720f1b0df1c63d26bd1/LICENSE). Twenty-four of the 183 selected BoundedGaps files were modified for compatibility in the accepted local package. Preserve the license and original notices, and identify those modifications in local generation records. Fetch the pinned compatibility patches where needed; do not relabel an upstream patch as newly authored work. Distinguish `original_sha256`, accepted local `packaged_sha256`, and public-generation hashes in manifests. A newly appended notice changes the latter hash and must be recorded honestly.

Third-party rights review remains unresolved for the specified plby material. The repository may document and submit its actual new contribution while disclosing this issue; it must not affirm that unknown permission has been obtained. The award maintainers determine acceptance and any further evidence required. No upstream authorization request or third-party contact was made as part of this publication workflow.
